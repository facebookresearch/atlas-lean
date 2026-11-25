/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientFiniteEuler
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.KrullDimension.Module
public import MathlibExt.RingTheory.Length.AnnihilatorQuotient

/-!
# Prime-filtration decomposition of actual finite-family Koszul Euler characteristics

The finite quotient by the coefficient ideal plus the module annihilator passes
along both maps of an actual short exact sequence. Noetherian prime-filtration
induction therefore expresses the original coefficient tensor Euler invariant as
an actual finite sum of prime-quotient invariants. The decomposition also records
all localized module lengths, with repetitions retaining their multiplicities.

The localized-length arguments follow the one-element decomposition in
`MathlibExt/Algebra/Homology/ElementEulerPrimeFiltration.lean` at revision
`c4e2bd199fcf972fd1c53cc07188316ab36f0189`. The coefficient family and its
Euler characteristic here are the existing genuine Koszul tensor objects.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace KoszulComplex

variable (R : Type u) [CommRing R] {n : ℕ}

/-- Finite length of a quotient passes to the quotient by a larger ideal. -/
theorem familyQuotient_length_ne_top_of_annihilator_le
    (a : Fin n → R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (hAnn : Module.annihilator R M ≤ Module.annihilator R N)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R N)) ≠ ⊤ := by
  exact Module.length_ne_top_of_finite_of_ideal_le_annihilator R
    (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R N))
    (Ideal.span (Set.range a) ⊔ Module.annihilator R M)
    (by rw [Ideal.annihilator_quotient]; exact sup_le_sup_left hAnn _) hquot

/-- An actual coefficient isomorphism induces an isomorphism of the original
full-family tensor complexes. -/
def familyTensorCoefficientIso (a : Fin n → R) {M N : ModuleCat.{v} R}
    (e : M ≅ N) :
    familyTensorCoefficientComplex R a M ≅ familyTensorCoefficientComplex R a N :=
  (NatIso.mapHomologicalComplex
    ((coefficientTensoringLeft R).mapIso e)
      (ComplexShape.down ℕ)).app (familyComplex R a)

/-- The canonical mixed-universe tensor equivalence when the original
coefficient module is lifted. -/
def familyTensorCoefficientUliftTermEquiv (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    (ULift.{w} M ⊗[R] ((familyComplex R a).X j)) ≃ₗ[R]
      ULift.{w} (M ⊗[R] ((familyComplex R a).X j)) :=
  TensorProduct.congr (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M)
    (LinearEquiv.refl R ((familyComplex R a).X j)) ≪≫ₗ ULift.moduleEquiv.symm

/-- The original coefficient tensor complex commutes with the canonical
module universe lift, retaining its actual terms and differential maps. -/
def familyTensorCoefficientUliftComplexIso (a : Fin n → R) (M : ModuleCat.{v} R) :
    familyTensorCoefficientComplex R a ((ModuleCat.uliftFunctor.{w, v} R).obj M) ≅
      ((ModuleCat.uliftFunctor.{w, max u v} R).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (familyTensorCoefficientComplex R a M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (familyTensorCoefficientUliftTermEquiv R a M j).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro m
      apply LinearMap.ext
      intro x
      rfl)

/-- Actual native homology commutes with the earned coefficient lift,
through the exact canonical module lift functor. -/
def familyTensorCoefficientUliftHomologyIso (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    (familyTensorCoefficientComplex R a ((ModuleCat.uliftFunctor.{w, v} R).obj M)).homology j ≅
      (ModuleCat.uliftFunctor.{w, max u v} R).obj ((familyTensorCoefficientComplex R a M).homology j) :=
  HomologicalComplex.homologyMapIso (familyTensorCoefficientUliftComplexIso R a M) j ≪≫
    (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) j
      (ModuleCat.uliftFunctor.{w, max u v} R)).app (familyTensorCoefficientComplex R a M)

/-- A coefficient linear equivalence in independent universes preserves
every actual full-family tensor homology length. -/
theorem familyTensorCoefficient_homology_length_eq_of_equiv
    (a : Fin n → R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (j : ℕ) :
    Module.length R ((familyTensorCoefficientComplex R a (ModuleCat.of R M)).homology j) =
      Module.length R ((familyTensorCoefficientComplex R a (ModuleCat.of R N)).homology j) := by
  let eLift : ULift.{max u v w} M ≃ₗ[R] ULift.{max u v w} N :=
    (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[R] M) ≪≫ₗ e ≪≫ₗ
      (ULift.moduleEquiv : ULift.{max u v w} N ≃ₗ[R] N).symm
  let HM := (familyTensorCoefficientComplex R a (ModuleCat.of R M)).homology j
  let HN := (familyTensorCoefficientComplex R a (ModuleCat.of R N)).homology j
  have hMu := (ULift.moduleEquiv : ULift.{max u v w} HM ≃ₗ[R] HM).length_eq
  have hNu := (ULift.moduleEquiv : ULift.{max u v w} HN ≃ₗ[R] HN).length_eq
  have hM := (familyTensorCoefficientUliftHomologyIso.{u, v, max u v w}
    R a (ModuleCat.of R M) j).toLinearEquiv.length_eq
  have hN := (familyTensorCoefficientUliftHomologyIso.{u, w, max u v w}
    R a (ModuleCat.of R N) j).toLinearEquiv.length_eq
  have hE := (HomologicalComplex.homologyMapIso
    (familyTensorCoefficientIso R a eLift.toModuleIso) j).toLinearEquiv.length_eq
  exact hMu.symm.trans (hM.symm.trans (hE.trans (hN.trans hNu)))

/-- The actual full-family Euler invariant is preserved by a coefficient
linear equivalence in independent module universes. -/
theorem familyTensorCoefficientEuler_equiv [IsNoetherianRing R]
    (a : Fin n → R) {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (e : M ≃ₗ[R] N)
    (hM : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (hN : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R N)) ≠ ⊤) :
    familyTensorCoefficientEuler R a (ModuleCat.of R M) hM =
      familyTensorCoefficientEuler R a (ModuleCat.of R N) hN := by
  rw [familyTensorCoefficientEuler_eq, familyTensorCoefficientEuler_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [familyTensorCoefficient_homology_length_eq_of_equiv R a e j]

/-- Actual coefficient additivity under the original annihilator-quotient
finiteness premise, without finite length of any coefficient module. -/
theorem familyTensorCoefficientEuler_additive [IsNoetherianRing R]
    (a : Fin n → R) {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₃]
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (h₁ : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M₁)) ≠ ⊤)
    (h₂ : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M₂)) ≠ ⊤)
    (h₃ : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M₃)) ≠ ⊤) :
    familyTensorCoefficientEuler R a (ModuleCat.of R M₂) h₂ =
      familyTensorCoefficientEuler R a (ModuleCat.of R M₁) h₁ +
        familyTensorCoefficientEuler R a (ModuleCat.of R M₃) h₃ := by
  let S : ShortComplex (ModuleCat.{v} R) :=
    ShortComplex.mk (ModuleCat.ofHom i) (ModuleCat.ofHom p)
      (ModuleCat.hom_ext (LinearMap.ext fun x => hip.apply_apply_eq_zero x))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hip
      mono_f := (ModuleCat.mono_iff_injective _).mpr hi
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hp }
  exact familyTensorCoefficientEuler_shortExact R a S hS
    (familyTensorCoefficientFiniteLength R a _ h₁)
    (familyTensorCoefficientFiniteLength R a _ h₂)
    (familyTensorCoefficientFiniteLength R a _ h₃)

end KoszulComplex

namespace Module

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n : ℕ}

/-- A prime quotient with the finite quotient needed for the actual
full-family Koszul Euler invariant. -/
structure KoszulFamilyEulerPrimeFactor (a : Fin n → R) where
  /-- The prime ideal indexing the genuine coefficient factor. -/
  prime : PrimeSpectrum R
  /-- Finite quotient by the original family together with this prime. -/
  quotient_length_ne_top :
    Module.length R (R ⧸ (Ideal.span (Set.range a) ⊔ prime.asIdeal)) ≠ ⊤

/-- The genuine Koszul tensor Euler contribution of a prime factor. -/
def KoszulFamilyEulerPrimeFactor.value {a : Fin n → R}
    (f : KoszulFamilyEulerPrimeFactor R a) : ℤ :=
  KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R (R ⧸ f.prime.asIdeal))
    (by
      change Module.length R
        (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R (R ⧸ f.prime.asIdeal))) ≠ ⊤
      rw [Ideal.annihilator_quotient]
      exact f.quotient_length_ne_top)

/-- Actual localized length of a prime-quotient factor at another prime. -/
def KoszulFamilyEulerPrimeFactor.localLengthAt {a : Fin n → R}
    (f : KoszulFamilyEulerPrimeFactor R a) (q : PrimeSpectrum R) : ENat :=
  Module.length (Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl (R ⧸ f.prime.asIdeal))

/-- A prime-filtration expression for the original full-family Koszul tensor
Euler characteristic. Its localized-length equation retains every multiplicity. -/
structure KoszulFamilyEulerPrimeDecomposition
    (a : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] where
  /-- Earned finite-length data for the original coefficient tensor complex. -/
  finiteLength : HomologicalComplex.FiniteLengthHomologyData R
    (KoszulComplex.familyTensorCoefficientComplex R a (ModuleCat.of R M))
  /-- The actual finite factor list, with repetitions. -/
  factors : List (KoszulFamilyEulerPrimeFactor R a)
  /-- Every factor lies in the support of the original module. -/
  factor_mem_support : ∀ f ∈ factors, f.prime ∈ Module.support R M
  /-- Every original localized length is the sum of the localized factor lengths. -/
  localized_length_eq : ∀ q : PrimeSpectrum R,
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) =
      (factors.map fun f => f.localLengthAt R q).sum
  /-- The actual alternating homology sum equals its prime-filtration sum. -/
  eq_sum : HomologicalComplex.finiteLengthEulerCharacteristic R finiteLength =
    (factors.map (KoszulFamilyEulerPrimeFactor.value R)).sum

/-- The earned decomposition computes the canonical actual coefficient Euler
invariant, independently of the finite-length data used by the decomposition. -/
theorem KoszulFamilyEulerPrimeDecomposition.eq_sum_familyTensorCoefficientEuler
    {a : Fin n → R} {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : KoszulFamilyEulerPrimeDecomposition R a M)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot =
      (d.factors.map (KoszulFamilyEulerPrimeFactor.value R)).sum :=
  (HomologicalComplex.finiteLengthEulerCharacteristic_eq_of_data R
    (KoszulComplex.familyTensorCoefficientFiniteLength R a (ModuleCat.of R M) hquot)
      d.finiteLength).trans d.eq_sum

/-- Every actual finite module with finite original coefficient/annihilator
quotient admits a genuine full-family prime-filtration Euler decomposition. -/
theorem exists_koszulFamilyEulerPrimeDecomposition
    (a : Fin n → R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤) :
    Nonempty (KoszulFamilyEulerPrimeDecomposition R a M) := by
  revert hquot
  induction (inferInstance : Module.Finite R M) using
      IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
      intro hquot
      refine ⟨({
        finiteLength := KoszulComplex.familyTensorCoefficientFiniteLength R a (ModuleCat.of R N) hquot
        factors := []
        factor_mem_support := by simp
        localized_length_eq := ?_
        eq_sum := ?_ } : KoszulFamilyEulerPrimeDecomposition R a N)⟩
      · intro q
        simp only [List.map_nil, List.sum_nil]
        rw [Module.length_eq_zero_iff]
        infer_instance
      change KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R N) hquot = 0
      rw [KoszulComplex.familyTensorCoefficientEuler_eq]
      apply Finset.sum_eq_zero
      intro j _
      have hj : Module.length R
          ((KoszulComplex.familyTensorCoefficientComplex R a (ModuleCat.of R N)).homology j) = 0 := by
        rw [Module.length_eq_zero_iff]
        have hX : IsZero ((KoszulComplex.familyTensorCoefficientComplex R a (ModuleCat.of R N)).X j) :=
          ModuleCat.isZero_iff_subsingleton.mpr (by
            change Subsingleton (N ⊗[R] ((KoszulComplex.familyComplex R a).X j))
            infer_instance)
        exact ModuleCat.isZero_iff_subsingleton.mp
          (HomologicalComplex.ExactAt.of_isZero hX).isZero_homology
      simp [hj]
  | quotient N p e =>
      intro hquot
      have hpData : Module.length R
          (R ⧸ (Ideal.span (Set.range a) ⊔ p.asIdeal)) ≠ ⊤ := by
        rw [e.annihilator_eq, Ideal.annihilator_quotient] at hquot
        exact hquot
      let factor : KoszulFamilyEulerPrimeFactor R a :=
        { prime := p, quotient_length_ne_top := hpData }
      have hpSupport : p ∈ Module.support R N :=
        Module.mem_support_iff_of_finite.mpr (by
          rw [e.annihilator_eq, Ideal.annihilator_quotient])
      refine ⟨({
        finiteLength := KoszulComplex.familyTensorCoefficientFiniteLength R a (ModuleCat.of R N) hquot
        factors := [factor]
        factor_mem_support := ?_
        localized_length_eq := ?_
        eq_sum := ?_ } : KoszulFamilyEulerPrimeDecomposition R a N)⟩
      · intro f hf
        simp only [List.mem_singleton] at hf
        subst f
        exact hpSupport
      · intro q
        let S := q.asIdeal.primeCompl
        let Q := Localization.AtPrime q.asIdeal
        let eLoc : LocalizedModule S N ≃ₗ[Q]
            LocalizedModule S (R ⧸ p.asIdeal) :=
          LinearEquiv.ofBijective (LocalizedModule.map S e.toLinearMap)
            ⟨LocalizedModule.map_injective S e.toLinearMap e.injective,
              LocalizedModule.map_surjective S e.toLinearMap e.surjective⟩
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact eLoc.length_eq
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact KoszulComplex.familyTensorCoefficientEuler_equiv R a e hquot
        (by
          change Module.length R
            (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R (R ⧸ p.asIdeal))) ≠ ⊤
          rw [Ideal.annihilator_quotient]
          exact hpData)
  | exact N₁ N₂ N₃ i p hi hp hip ih₁ ih₃ =>
      intro hquot
      have hquot₁ := KoszulComplex.familyQuotient_length_ne_top_of_annihilator_le
        R a (i.annihilator_le_of_injective hi) hquot
      have hquot₃ := KoszulComplex.familyQuotient_length_ne_top_of_annihilator_le
        R a (p.annihilator_le_of_surjective hp) hquot
      obtain ⟨d₁⟩ := ih₁ hquot₁
      obtain ⟨d₃⟩ := ih₃ hquot₃
      refine ⟨({
        finiteLength := KoszulComplex.familyTensorCoefficientFiniteLength R a (ModuleCat.of R N₂) hquot
        factors := d₁.factors ++ d₃.factors
        factor_mem_support := by
          intro f hf
          rw [List.mem_append] at hf
          rcases hf with hf | hf
          · exact Module.support_subset_of_injective i hi (d₁.factor_mem_support f hf)
          · exact Module.support_subset_of_surjective p hp (d₃.factor_mem_support f hf)
        localized_length_eq := ?_
        eq_sum := ?_ } : KoszulFamilyEulerPrimeDecomposition R a N₂)⟩
      · intro q
        let S := q.asIdeal.primeCompl
        let Q := Localization.AtPrime q.asIdeal
        let iLoc := LocalizedModule.map S i
        let pLoc := LocalizedModule.map S p
        calc
          Module.length Q (LocalizedModule S N₂) =
              Module.length Q (LocalizedModule S N₁) + Module.length Q (LocalizedModule S N₃) :=
            Module.length_eq_add_of_exact iLoc pLoc
              (LocalizedModule.map_injective S i hi)
              (LocalizedModule.map_surjective S p hp)
              (LocalizedModule.map_exact S i p hip)
          _ = (d₁.factors.map fun f => f.localLengthAt R q).sum +
              (d₃.factors.map fun f => f.localLengthAt R q).sum := by
            rw [d₁.localized_length_eq q, d₃.localized_length_eq q]
          _ = ((d₁.factors ++ d₃.factors).map fun f => f.localLengthAt R q).sum := by simp
      calc
        KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R N₂) hquot =
            KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R N₁) hquot₁ +
              KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R N₃) hquot₃ :=
          KoszulComplex.familyTensorCoefficientEuler_additive R a i p hi hp hip hquot₁ hquot hquot₃
        _ = (d₁.factors.map (KoszulFamilyEulerPrimeFactor.value R)).sum +
            (d₃.factors.map (KoszulFamilyEulerPrimeFactor.value R)).sum := by
          rw [d₁.eq_sum_familyTensorCoefficientEuler R hquot₁,
            d₃.eq_sum_familyTensorCoefficientEuler R hquot₃]
        _ = ((d₁.factors ++ d₃.factors).map (KoszulFamilyEulerPrimeFactor.value R)).sum := by simp

omit [IsNoetherianRing R] in
/-- Two bundled prime factors are equal exactly when their primes are equal;
the finite-length field is proof-irrelevant. -/
theorem KoszulFamilyEulerPrimeFactor.eq_iff_prime_eq
    {a : Fin n → R} {f g : KoszulFamilyEulerPrimeFactor R a} :
    f = g ↔ f.prime = g.prime := by
  constructor
  · exact fun h => congrArg KoszulFamilyEulerPrimeFactor.prime h
  · intro h
    cases f with
    | mk fp fh =>
      cases g with
      | mk gp gh =>
        dsimp only at h
        subst gp
        rfl

omit [IsNoetherianRing R] in
open Classical in
/-- Counting a bundled factor is the same as counting factors with its
prime. -/
theorem KoszulFamilyEulerPrimeFactor.count_eq_countP_prime
    {a : Fin n → R} (l : List (KoszulFamilyEulerPrimeFactor R a))
    (f : KoszulFamilyEulerPrimeFactor R a) :
    l.count f = l.countP (fun g => decide (g.prime = f.prime)) := by
  induction l with
  | nil => simp
  | cons g l ih =>
      by_cases h : g.prime = f.prime
      · have hgf : g = f :=
          (KoszulFamilyEulerPrimeFactor.eq_iff_prime_eq R).mpr h
        subst g
        simp [ih]
      · have hgf : g ≠ f := fun h' => h <|
          (KoszulFamilyEulerPrimeFactor.eq_iff_prime_eq R).mp h'
        simp [h, hgf, ih]

omit [IsNoetherianRing R] in
/-- A prime factor has local length one at its own prime. -/
theorem KoszulFamilyEulerPrimeFactor.localLengthAt_eq_one
    {a : Fin n → R} (f : KoszulFamilyEulerPrimeFactor R a) :
    f.localLengthAt R f.prime = 1 := by
  let S := f.prime.asIdeal.primeCompl
  let Q := Localization.AtPrime f.prime.asIdeal
  have hmap : LocalizedModule.mkLinearMap S R = Algebra.linearMap R Q := by
    apply LinearMap.ext
    intro x
    rfl
  have hloc : Submodule.localized S f.prime.asIdeal =
      f.prime.asIdeal.map (algebraMap R Q) := by
    simpa only [Submodule.localized, hmap] using
      (Ideal.localized'_eq_map Q S f.prime.asIdeal)
  let e : LocalizedModule S (R ⧸ f.prime.asIdeal) ≃ₗ[Q]
      f.prime.asIdeal.ResidueField :=
    (localizedQuotientEquiv S f.prime.asIdeal).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (by
        rw [hloc, Localization.AtPrime.map_eq_maximalIdeal])
  change Module.length Q
    (LocalizedModule S (R ⧸ f.prime.asIdeal)) = 1
  have hsimple : IsSimpleModule Q f.prime.asIdeal.ResidueField :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨IsLocalRing.maximalIdeal Q, inferInstance, ⟨LinearEquiv.refl Q _⟩⟩
  let : IsSimpleModule Q f.prime.asIdeal.ResidueField := hsimple
  exact e.length_eq.trans (Module.length_eq_one Q _)

omit [IsNoetherianRing R] in
/-- A prime factor localizes to zero at a prime not containing it. -/
theorem KoszulFamilyEulerPrimeFactor.localLengthAt_eq_zero_of_not_le
    {a : Fin n → R} (f : KoszulFamilyEulerPrimeFactor R a) (q : PrimeSpectrum R)
    (h : ¬ f.prime.asIdeal ≤ q.asIdeal) :
    f.localLengthAt R q = 0 := by
  change Module.length (Localization.AtPrime q.asIdeal)
    (LocalizedModule q.asIdeal.primeCompl (R ⧸ f.prime.asIdeal)) = 0
  rw [Module.length_eq_zero_iff]
  apply (LocalizedModule.subsingleton_iff
    (R := R) (M := R ⧸ f.prime.asIdeal)
      (S := q.asIdeal.primeCompl)).mpr
  obtain ⟨a, ha, haq⟩ := IsConcreteLE.not_le_iff_exists.mp h
  intro x
  refine ⟨a, haq, ?_⟩
  change a • x = 0
  rw [show (a : R) • x = Ideal.Quotient.mk f.prime.asIdeal a * x by rfl,
    Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]

open Classical in
/-- At a prime minimal in the module support, the localized length is the
number of occurrences of that prime in the decomposition's factor list. -/
theorem KoszulFamilyEulerPrimeDecomposition.localized_length_eq_countP_of_minimal
    {M : Type v} [AddCommGroup M] [Module R M] {a : Fin n → R}
    (d : KoszulFamilyEulerPrimeDecomposition R a M) (q : PrimeSpectrum R)
    (hmin : ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
      p.asIdeal ≤ q.asIdeal → p = q) :
    Module.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule q.asIdeal.primeCompl M) =
      (d.factors.countP fun f => decide (f.prime = q) : ℕ) := by
  rw [d.localized_length_eq q]
  have hfactor : ∀ f ∈ d.factors,
      f.localLengthAt R q =
        if f.prime = q then (1 : ENat) else 0 := by
    intro f hf
    by_cases heq : f.prime = q
    · subst q
      simp only [↓reduceIte]
      exact f.localLengthAt_eq_one R
    · simp only [heq, ↓reduceIte]
      apply f.localLengthAt_eq_zero_of_not_le R q
      intro hle
      exact heq (hmin f.prime (d.factor_mem_support f hf) hle)
  rw [List.map_congr_left hfactor]
  induction d.factors with
  | nil => simp
  | cons f fs ih =>
      by_cases h : f.prime = q <;>
        simp [h, ih, add_comm]

open Classical in
/-- Repetitions of every nonzero-contributing prime factor are the original
localized module lengths once that prime is minimal in the module support. -/
theorem KoszulFamilyEulerPrimeDecomposition.eq_sum_localizedLength_mul
    {a : Fin n → R} {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : KoszulFamilyEulerPrimeDecomposition R a M)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (hmin : ∀ f ∈ d.factors, f.value R ≠ 0 →
      ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
        p.asIdeal ≤ f.prime.asIdeal → p = f.prime) :
    KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot =
      ∑ f ∈ d.factors.toFinset,
        ((Module.length (Localization.AtPrime f.prime.asIdeal)
          (LocalizedModule f.prime.asIdeal.primeCompl M)).toNat : ℤ) * f.value R := by
  calc
    KoszulComplex.familyTensorCoefficientEuler R a (ModuleCat.of R M) hquot =
        (d.factors.map (KoszulFamilyEulerPrimeFactor.value R)).sum :=
      d.eq_sum_familyTensorCoefficientEuler R hquot
    _ = ∑ f ∈ d.factors.toFinset, d.factors.count f • f.value R :=
      Finset.sum_list_map_count d.factors (KoszulFamilyEulerPrimeFactor.value R)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      have hfList : f ∈ d.factors := by simpa using hf
      by_cases hzero : f.value R = 0
      · simp [hzero]
      · have hlocal := d.localized_length_eq_countP_of_minimal R f.prime (hmin f hfList hzero)
        have hcount := f.count_eq_countP_prime R d.factors
        have hNat := congrArg ENat.toNat hlocal
        rw [ENat.toNat_natCast, ← hcount] at hNat
        rw [hNat]
        simp only [nsmul_eq_mul]

end Module

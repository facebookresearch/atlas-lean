/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMFormalModule

/-!
# Tests for formal coordinates, formal `O_D`-modules and QM fake elliptic curves
-/

@[expose] public section

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped Quaternion

universe u

/-- A fake elliptic curve that is a formal module over `X` is one via some
coordinate family. -/
private theorem exactSource {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {q : ℕ} [Fact q.Prime] {B : Type u} [CommRing B]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (h : E.IsFormalModuleOf coord X) :
    ∃ θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2,
      E.IsFormalModuleVia coord X θ :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleOf_iff E coord X).mp h

/-- The formal-coordinate predicates apply to fake elliptic curves over a
ring in any universe: a formal-module structure via `θ` makes `θ` formal
coordinates for the formal group of `X`. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    {B : Type u} [CommRing B] (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2)
    (h : E.IsFormalModuleVia coord X θ) : E.L.IsFormalCoordinates X.F θ :=
  h.1

/-- The identity series is a law homomorphism for every formal group. -/
example {B : Type u} [CommRing B] (F : MvFormalGroup 2 B) :
    IsLawHom F F (Series.id B) :=
  IsLawHom.id F

/-- Kernel degree of the action of `p` is the height predicate. -/
example {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
    (X : FormalODModule p B) (h : ℕ) :
    X.HasHeight h ↔ FormalODModule.HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h) :=
  Iff.rfl

open CategoryTheory AlgebraicGeometry in
/-- Formal coordinates are injective on points infinitesimal along a
square-zero ideal, so the constant family at the identity point is not a
system of formal coordinates over a nontrivial ring. -/
example {B : Type u} [CommRing B] [Nontrivial B] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 1 B) :
    ¬ L.IsFormalCoordinates F (fun _ _ _ _ => L.one _) := by
  rintro ⟨-, h⟩
  have hJ : Ideal.span {(DualNumber.eps : DualNumber B)} ^ (1 + 1) = ⊥ := by
    rw [Ideal.span_singleton_pow, pow_two, DualNumber.eps_mul_eps,
      Ideal.span_singleton_eq_bot]
  have hst := (h (DualNumber B) _ 1 hJ).2.1 0 (fun _ => DualNumber.eps)
    (fun _ => Ideal.zero_mem _) (fun _ => Ideal.mem_span_singleton_self _) rfl
  simpa using congrArg (fun s => TrivSqZeroExt.snd (s 0)) hst

open CategoryTheory AlgebraicGeometry in
/-- `IsFormalCompletionAlong` is only a compatibility condition: the constant
families at the identity point, which by the previous example are not
formal coordinates over a nontrivial ring, satisfy it for the identity
morphism and any series. -/
example {B : Type u} [CommRing B] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (φ : Fin 1 → MvPowerSeries (Fin 1) B) :
    CerednikDrinfeld.QM.IsFormalCompletionAlong (g := 1) (g' := 1)
      (fun _ _ _ _ => L.one _) (fun _ _ _ _ => L.one _) (𝟙 A)
      (Category.id_comp f) φ := by
  intro B' _ _ J n _ s _
  apply Over.OverMorphism.ext
  simp

/-- `Λ` acts on a fake elliptic curve as a unital monoid action by
endomorphisms, with no membership side conditions. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    ↥Λ →* CategoryTheory.End E.A where
  toFun x := .of (E.act x)
  map_one' := CategoryTheory.End.ext (by simp [E.act_one])
  map_mul' x y := CategoryTheory.End.ext (by simp [E.act_mul])

open CategoryTheory in
/-- Hecke neighbours are taken at a prime, and both composites are the
action of that prime. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type} [CommRing S]
    {E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour ℓ E E') :
    ℓ.Prime ∧ ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A),
      φ ≫ ψ = E.act (ℓ : ↥Λ) ∧ ψ ≫ φ = E'.act (ℓ : ↥Λ) := by
  obtain ⟨hℓ, φ, -, ψ, -, -, -, -, -, -, -, hc, -, -⟩ := h
  exact ⟨hℓ, φ, ψ, hc⟩

/-- `0`, `1` and the composite `4` give no Hecke neighbours. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 0 E E' ∧
      ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 1 E E' ∧
      ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 4 E E' :=
  ⟨fun h => Nat.not_prime_zero h.1, fun h => Nat.not_prime_one h.1, fun h => by
    have := h.1.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩
    omega⟩

/-- An isogeny of formal modules is an `O_D`-homomorphism: it commutes
with the action and with `varpi`. -/
example {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
    {X Y : FormalODModule p B} {φ : Series B} {h : ℕ}
    (hφ : FormalODModule.IsIsogenyOfHeight X Y φ h) :
    (∀ a, φ.comp (X.act a) = (Y.act a).comp φ) ∧
      φ.comp X.varpi = Y.varpi.comp φ :=
  hφ.1.2

namespace MvFormalGroupTest

open MvPowerSeries MvFormalGroup

/-- Truncating at an order that is positive in the variable `v` keeps `X v`. -/
private theorem trunc'_X_of_one_le {σ R : Type*} [DecidableEq σ]
    [CommSemiring R] {n : σ →₀ ℕ} {v : σ} (hv : 1 ≤ n v) :
    trunc' R n (X v) = MvPolynomial.X v := by
  ext m
  rw [coeff_trunc', coeff_X, MvPolynomial.coeff_X]
  by_cases hm : m = Finsupp.single v 1
  · subst hm
    simp [Finsupp.single_le_iff, hv]
  · simp [hm, Ne.symm hm]

/-- Truncating at an order that is zero in the variable `v` drops `X v`. -/
private theorem trunc'_X_of_eq_zero {σ R : Type*} [DecidableEq σ]
    [CommSemiring R] {n : σ →₀ ℕ} {v : σ} (hv : n v = 0) :
    trunc' R n (X v) = 0 := by
  ext m
  rw [coeff_trunc', coeff_X]
  by_cases hm : m = Finsupp.single v 1
  · subst hm
    simp [Finsupp.single_le_iff, hv]
  · simp [hm]

/-- Truncating at the constant order `1` keeps `X₀ X₁`, whose exponents are
both `1`, although its total degree is `2`. -/
private theorem trunc'_X_mul_X :
    trunc' ℤ (Finsupp.equivFunOnFinite.symm fun _ => 1)
        (X 0 * X 1 : MvPowerSeries (Fin 2) ℤ) =
      MvPolynomial.X 0 * MvPolynomial.X 1 := by
  rw [X, X, monomial_mul_monomial, MvPolynomial.X, MvPolynomial.X,
    MvPolynomial.monomial_mul_monomial]
  ext m
  rw [coeff_trunc', coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases hm : m = Finsupp.single 0 1 + Finsupp.single 1 1
  · subst hm
    have hle : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ≤
        Finsupp.equivFunOnFinite.symm fun _ => 1 := by
      intro i
      fin_cases i <;> simp
    simp [hle]
  · simp [hm, Ne.symm hm]

/-- A family of power series is a homomorphism of additive formal groups
when substituting a sum of two points gives the sum of the substitutions. -/
private def addMvHom {g h : ℕ} {R : Type*} [CommRing R]
    (φ : Fin h → MvPowerSeries (Fin g) R) (hφ : ∀ i, (φ i).constantCoeff = 0)
    (hadd : ∀ i, subst (addMv g R).toPowerSeries (φ i) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ i) +
        subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (φ i)) :
    Hom (addMv g R) (addMv h R) where
  toPowerSeries := φ
  constantCoeff_eq_zero := hφ
  subst_eq i := by
    have hz : ∀ s : Fin h ⊕ Fin h, ((Sum.elim
        (fun j => subst
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ j))
        fun j => subst
          (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ j))
        s).constantCoeff = 0 := by
      rintro (j | j) <;>
        exact constantCoeff_subst_eq_zero
          (hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _)
          (fun l => constantCoeff_X _) (hφ j)
    rw [hadd i]
    exact (subst_X_add_X hz (Sum.inl i) (Sum.inr i)).symm

private theorem additive_X {g : ℕ} {R : Type*} [CommRing R] (s : Fin g) :
    subst (addMv g R).toPowerSeries (X s : MvPowerSeries (Fin g) R) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (X s : MvPowerSeries (Fin g) R) +
        subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (X s : MvPowerSeries (Fin g) R) := by
  have hl : HasSubst
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hr : HasSubst
      (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  rw [subst_X (addMv g R).hasSubst_toPowerSeries, subst_X hl, subst_X hr]
  rfl

private theorem additive_X_add_X {g : ℕ} {R : Type*} [CommRing R]
    (s t : Fin g) :
    subst (addMv g R).toPowerSeries (X s + X t : MvPowerSeries (Fin g) R) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (X s + X t : MvPowerSeries (Fin g) R) +
        subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (X s + X t : MvPowerSeries (Fin g) R) := by
  rw [subst_X_add_X (addMv g R).constantCoeff_eq_zero,
    subst_X_add_X
      (a := fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun l => constantCoeff_X _),
    subst_X_add_X
      (a := fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
      (fun l => constantCoeff_X _)]
  change X (Sum.inl s) + X (Sum.inr s) + (X (Sum.inl t) + X (Sum.inr t)) = _
  abel

/-- The shear `(X₀, X₁) ↦ (X₀ + X₁, X₁)` of the additive formal group. -/
private noncomputable def shear₀ : Hom (addMv 2 ℤ) (addMv 2 ℤ) :=
  addMvHom ![X 0 + X 1, X 1] (by intro i; fin_cases i <;> simp) (by
    intro i
    fin_cases i
    · exact additive_X_add_X 0 1
    · exact additive_X 1)

/-- The shear `(X₀, X₁) ↦ (X₀, X₀ + X₁)` of the additive formal group. -/
private noncomputable def shear₁ : Hom (addMv 2 ℤ) (addMv 2 ℤ) :=
  addMvHom ![X 0, X 0 + X 1] (by intro i; fin_cases i <;> simp) (by
    intro i
    fin_cases i
    · exact additive_X 0
    · exact additive_X_add_X 0 1)

/-- Composition substitutes the right-hand homomorphism into the left-hand
one, so it applies the right-hand homomorphism first. -/
example {g h k : ℕ} {R : Type*} [CommRing R] {F : MvFormalGroup g R}
    {G : MvFormalGroup h R} {H : MvFormalGroup k R} (ψ : Hom G H) (φ : Hom F G)
    (i : Fin k) :
    (ψ.comp φ).toPowerSeries i = subst φ.toPowerSeries (ψ.toPowerSeries i) :=
  rfl

/-- The identity homomorphism is a two-sided unit for composition. -/
example {g h : ℕ} {R : Type*} [CommRing R] {F : MvFormalGroup g R}
    {G : MvFormalGroup h R} (φ : Hom F G) :
    (Hom.id G).comp φ = φ ∧ φ.comp (Hom.id F) = φ :=
  ⟨Hom.ext (funext fun i => subst_X φ.hasSubst_toPowerSeries i),
    Hom.ext (funext fun i => congrFun subst_self (φ.toPowerSeries i))⟩

/-- The two shears do not commute, and `shear₁.comp shear₀` applies `shear₀`
first: its second coordinate is `X₀ + 2 X₁`, while the other order gives
`X₀ + X₁`. -/
example : (shear₁.comp shear₀).toPowerSeries 1 = X 0 + X 1 + X 1 ∧
    (shear₀.comp shear₁).toPowerSeries 1 = X 0 + X 1 ∧
    shear₁.comp shear₀ ≠ shear₀.comp shear₁ := by
  have h₁ : (shear₁.comp shear₀).toPowerSeries 1 = X 0 + X 1 + X 1 := by
    change subst shear₀.toPowerSeries (X 0 + X 1) = _
    rw [subst_X_add_X shear₀.constantCoeff_eq_zero]
    rfl
  have h₂ : (shear₀.comp shear₁).toPowerSeries 1 = X 0 + X 1 := by
    change subst shear₁.toPowerSeries (X 1) = _
    rw [subst_X shear₁.hasSubst_toPowerSeries]
    rfl
  refine ⟨h₁, h₂, fun h => ?_⟩
  have hc := congrArg (fun φ : Hom (addMv 2 ℤ) (addMv 2 ℤ) =>
    coeff (Finsupp.single 1 1) (φ.toPowerSeries 1)) h
  simp only [h₁, h₂] at hc
  simp [coeff_X] at hc

/-- Base change of the additive formal group is the additive formal group. -/
example {g : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (addMv g R).map f = addMv g S :=
  MvFormalGroup.ext (funext fun i => by
    change MvPowerSeries.map f (X (Sum.inl i) + X (Sum.inr i)) =
      X (Sum.inl i) + X (Sum.inr i)
    simp)

/-- The `2`-series of the additive formal group doubles each coordinate. -/
private theorem addMv_nthSeries_two {g : ℕ} {R : Type*} [CommRing R] :
    (addMv g R).nthSeries 2 = fun i => X i + X i := by
  have h1 : (addMv g R).nthSeries 1 = fun i => X i := by
    funext i
    change subst (Sum.elim (fun _ => 0) fun j => X j)
      (X (Sum.inl i) + X (Sum.inr i)) = X i
    rw [subst_X_add_X (by rintro (j | j) <;> simp)]
    simp
  funext i
  change subst (Sum.elim ((addMv g R).nthSeries 1) fun j => X j)
    (X (Sum.inl i) + X (Sum.inr i)) = X i + X i
  rw [h1, subst_X_add_X (by rintro (j | j) <;> simp)]
  rfl

/-- At every point `a`, `nilEval 1` of the `2`-series of the additive formal
group is `a i + a i`; `nilEval` takes arbitrary points. -/
example {g : ℕ} {R B' : Type*} [CommRing R] [CommRing B'] [Algebra R B']
    (a : Fin g → B') (i : Fin g) :
    nilEval 1 ((addMv g R).nthSeries 2 i) a = a i + a i := by
  rw [addMv_nthSeries_two]
  simp [nilEval, trunc'_X_of_one_le]

/-- The additive law under `nilMul`, at arbitrary points: order one gives
the sum of the points, and order zero, which keeps only the constant
term, gives `0`. -/
example {g : ℕ} {R B' : Type*} [CommRing R] [CommRing B'] [Algebra R B']
    (s t : Fin g → B') :
    (addMv g R).nilMul 1 s t = s + t ∧ (addMv g R).nilMul 0 s t = 0 := by
  constructor
  · funext i
    change nilEval 1 (X (Sum.inl i) + X (Sum.inr i)) (Sum.elim s t) = s i + t i
    simp [nilEval, trunc'_X_of_one_le]
  · funext i
    change nilEval 0 (X (Sum.inl i) + X (Sum.inr i)) (Sum.elim s t) = 0
    simp [nilEval, trunc'_X_of_eq_zero]

/-- `nilEval` bounds each exponent, not the total degree: at every point,
`nilEval 1` keeps the monomial `X₀ X₁` of total degree `2`. -/
example (a : Fin 2 → ℤ) :
    nilEval 1 (X 0 * X 1 : MvPowerSeries (Fin 2) ℤ) a = a 0 * a 1 := by
  simp [nilEval, trunc'_X_mul_X]

/-- At a point with coordinates in an ideal `J` with `J ^ (n + 1) = ⊥`,
`nilEval n` is the evaluation of the truncation at total degree `n`: the
monomials of higher total degree that it keeps vanish there. -/
example {σ R B' : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    [CommRing B'] [Algebra R B'] {J : Ideal B'} {n : ℕ} (hJ : J ^ (n + 1) = ⊥)
    {a : σ → B'} (ha : ∀ i, a i ∈ J) (φ : MvPowerSeries σ R) :
    nilEval n φ a =
      ∑ d ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n) with d.degree ≤ n,
        algebraMap R B' (coeff d φ) * d.prod fun i k => a i ^ k := by
  rw [nilEval, trunc', truncFinset_apply, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]
  split_ifs with hd
  · rfl
  · have hmem : (d.prod fun i k => a i ^ k) ∈ J ^ d.degree := by
      rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (ha i) _
    have h0 := Ideal.pow_le_pow_right (I := J) (by omega : n + 1 ≤ d.degree) hmem
    rw [hJ, Ideal.mem_bot] at h0
    rw [h0, mul_zero]

end MvFormalGroupTest

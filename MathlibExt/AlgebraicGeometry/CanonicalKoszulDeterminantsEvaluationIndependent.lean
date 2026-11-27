/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Independence of canonical Koszul determinant evaluation

The value of a canonical evaluation is independent of its normalized comparison
and torsion, with the source assembly and all scalar/cochain inputs fixed.

Sources: Knudsen--Mumford, *The projectivity of the moduli space of stable
curves I*, Sections 1--2; Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.1,
pp108--110.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry MathlibExt.AlgebraicGeometry
open BoundedProjectiveDeterminants GlobalBoundedDeterminantModels
open ProjectiveDeterminantModules BoundedScalarDeterminants
open MathlibExt.AlgebraicGeometry.CanonicalKoszulDeterminants
open scoped TensorProduct ChangeOfRings

private theorem product_exact_eq (R : Type) [CommRing R]
    (M N : ModuleCat.{0} R) [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (E F : ShortExactDeterminant (LinearMap.snd R M N) (sndSurjective R M N)) :
    E = F := by
  have h : E.comparison = F.comparison := by
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    let z := ExteriorAlgebra.map (LinearMap.inr R M N) y.val
    have hz : ExteriorAlgebra.map (LinearMap.snd R M N) z = y.val := by
      simp [z, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    exact (E.normalization x y z hz).trans (F.normalization x y z hz).symm
  cases E
  cases F
  cases h
  rfl

private theorem sum_exact_eq (R : Type) [CommRing R] (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (E F : SumExactSources R Q) : E = F := by
  have h : E.exact = F.exact := by
    funext i t ss
    exact product_exact_eq R _ _ _ _
  cases E
  cases F
  cases h
  rfl

private theorem basis_coordinate_wedge (R : Type) [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] (r : ℕ)
    (b : Module.Basis (Fin r) R M)
    (h : ExteriorAlgebra.ιMulti R r b ∈ determinantSubmodule R M) :
    basisCoordinate R b (basisWedge R b h) = 1 := by
  change b.ExteriorAlgebra.coord Finset.univ (ExteriorAlgebra.ιMulti R r b) = 1
  have hb : b.ExteriorAlgebra Finset.univ = ExteriorAlgebra.ιMulti R r b := by
    rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_fin r)]
    change ExteriorAlgebra.ιMulti R r
      (b ∘ (Finset.univ.orderEmbOfFin (Finset.card_fin r))) = _
    rw [(Finset.univ.orderEmbOfFin (Finset.card_fin r)).strictMono.eq_id]
    rfl
  rw [← hb]
  simp

private def native_dual (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    S ⊗[R] Module.Dual R M ≃ₗ[S] Module.Dual S (S ⊗[R] M) := by
  let e := TensorProduct.comm R S (Module.Dual R M) ≪≫ₗ dualTensorHomEquiv R M S
  let e' : S ⊗[R] Module.Dual R M ≃ₗ[S] (M →ₗ[R] S) :=
    { e.toAddEquiv with
      map_smul' := fun s x ↦ by
        change e (s • x) = s • e x
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp [smul_add, hx, hy]
        | tmul t f =>
          ext m
          simp [e, TensorProduct.smul_tmul', Algebra.smul_def, mul_left_comm] }
  exact e' ≪≫ₗ LinearMap.liftBaseChangeEquiv S

private theorem native_dual_apply (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (s t : S) (f : Module.Dual R M) (v : M) :
    native_dual R S M (s ⊗ₜ[R] f) (t ⊗ₜ[R] v) = s * t * algebraMap R S (f v) := by
  change (LinearMap.liftBaseChangeEquiv S)
    ((dualTensorHomEquiv R M S) (f ⊗ₜ[R] s)) (t ⊗ₜ[R] v) = _
  change t • ((dualTensorHomEquiv R M S) (f ⊗ₜ[R] s)) v = _
  simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

private def native_sources (R S : CommRingCat.{0}) (g : R ⟶ S) :
    DeterminantScalarTensorModels.ScalarTensorSources g := by
  letI := g.hom.toAlgebra
  refine
    { unit := (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
      unit_normalized := ?_
      tensor := fun M N ↦ (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N).toModuleIso
      tensor_normalized := ?_
      dual := fun M hF hP ↦ (native_dual R S M).toModuleIso
      dual_normalized := ?_ }
  · intro s r
    change (TensorProduct.AlgebraTensorModule.rid R S S) (s • ((1 : S) ⊗ₜ[R] r)) = _
    simp [Algebra.smul_def]
    rfl
  · intro M N s m n
    change (TensorProduct.AlgebraTensorModule.distribBaseChange R S M N)
      (s • ((1 : S) ⊗ₜ[R] (m ⊗ₜ[R] n))) = (s • ((1 : S) ⊗ₜ[R] m)) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] n)
    simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · intro M hF hP s t f v
    change native_dual R S M (s • ((1 : S) ⊗ₜ[R] f)) (t • ((1 : S) ⊗ₜ[R] v)) =
      s * t * algebraMap R S (f v)
    convert native_dual_apply R S M s t f v using 1;
      simp [TensorProduct.smul_tmul', smul_eq_mul]

private theorem sum_coordinate_vector (R : Type) [CommRing R] (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (B : FreeSubsetBases R Q) (i : ℤ) (ss : List (Finset (Fin m))) :
    sumCoordinate R Q B i ss (sumVector R Q B i ss) = 1 := by
  induction ss with
  | nil => rfl
  | cons t ss ih =>
    change basisCoordinate R ((B t).basis (i-subsetDegree t))
      (basisWedge R ((B t).basis (i-subsetDegree t)) ((B t).wedge_mem (i-subsetDegree t))) *
        sumCoordinate R Q B i ss (sumVector R Q B i ss) = 1
    rw [basis_coordinate_wedge, ih, one_mul]

private theorem module_eqToHom_cast (R : Type) [CommRing R]
    (M N : ModuleCat.{0} R) (h : M = N) (k : (N : Type) = (M : Type)) (x : N) :
    (eqToHom h).hom (cast k x) = x := by
  cases h
  cases k
  rfl

private theorem assembled_term_coordinate (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (E : SumExactSources R Q) (T : TermAssembly R C Q) (B : FreeSubsetBases R Q) (i : ℤ) :
    ∃ f : Module.Dual R (term R C i), f (assembledTermVector R C Q E T B i) = 1 := by
  classical
  by_cases h : Even i
  · let e : term R C i ≅ ModuleCat.of R (determinantModule R (C.cochain.X i)) :=
      eqToIso (by simp [term, h])
    refine ⟨((sumCoordinate R Q B i (subsets m)).comp
      (termAssemblyDeterminant R C Q E T i).hom.hom).comp e.hom.hom, ?_⟩
    dsimp only [LinearMap.comp_apply]
    simp only [assembledTermVector, dite_eq_left h]
    change sumCoordinate R Q B i (subsets m)
      ((termAssemblyDeterminant R C Q E T i).hom
        (e.hom.hom (cast _ ((termAssemblyDeterminant R C Q E T i).inv
          (sumVector R Q B i (subsets m)))))) = 1
    dsimp only [e, eqToIso]
    rw [module_eqToHom_cast R (term R C i)]
    simpa using sum_coordinate_vector R m Q B i (subsets m)
  · let e : term R C i ≅
        ModuleCat.of R (Module.Dual R (determinantModule R (C.cochain.X i))) :=
      eqToIso (by simp [term, h])
    refine ⟨(dualCoordinate R ((termAssemblyDeterminant R C Q E T i).inv
      (sumVector R Q B i (subsets m)))).comp e.hom.hom, ?_⟩
    dsimp only [LinearMap.comp_apply, dualCoordinate]
    simp only [assembledTermVector, dite_eq_right h]
    change (e.hom.hom (cast _ ((sumCoordinate R Q B i (subsets m)).comp
      (termAssemblyDeterminant R C Q E T i).hom.hom)))
      ((termAssemblyDeterminant R C Q E T i).inv (sumVector R Q B i (subsets m))) = 1
    dsimp only [e, eqToIso]
    rw [module_eqToHom_cast R (term R C i)]
    simpa using sum_coordinate_vector R m Q B i (subsets m)

private theorem assembled_tensor_coordinate (R : Type) [CommRing R]
    (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (E : SumExactSources R Q) (T : TermAssembly R C Q) (B : FreeSubsetBases R Q) (is : List ℤ) :
    ∃ f : Module.Dual R (tensorTerms R C is), f (assembledTensorVector R C Q E T B is) = 1 := by
  induction is with
  | nil => exact ⟨LinearMap.id, rfl⟩
  | cons i is ih =>
    obtain ⟨f, hf⟩ := assembled_term_coordinate R C m Q E T B i
    obtain ⟨g, hg⟩ := ih
    refine ⟨TensorProduct.lift (f.smulRight g), ?_⟩
    change f (assembledTermVector R C Q E T B i) *
      g (assembledTensorVector R C Q E T B is) = 1
    rw [hf, hg, one_mul]

private theorem maps_eq_on_generator (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [Module.Invertible R M]
    [AddCommGroup N] [Module R N] (v : M) (f : Module.Dual R M) (hf : f v = 1)
    (a b : M →ₗ[R] N) (h : a v = b v) : a = b := by
  apply LinearMap.ext
  intro x
  have hx : f x • v = x := by
    let q := TensorProduct.lift (f.smulRight (LinearMap.id : M →ₗ[R] M))
    simpa [q, hf] using congrArg q (Module.Invertible.tmul_comm (m₁ := x) (m₂ := v))
  rw [← hx, map_smul, map_smul, h]

private theorem vector_naturality (R S : CommRingCat.{0}) (g : R ⟶ S)
    (M N : ModuleCat.{0} R) (f : M ⟶ N) (x : M) :
    (ModuleCat.extendScalars g.hom).map f (DeterminantScalarTensorModels.vector g M x) =
      DeterminantScalarTensorModels.vector g N (f x) := by
  rfl

namespace WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants

/-- Independence retains the same fixed source assembly and every scalar/cochain input. -/
public theorem evaluation_independent
    [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
    [∀ R : CommRingCat.{0}, ProjectiveSources R]
    (R : CommRingCat.{0}) (I : DeterminantSources)
    (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
    (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
    (T : TermAssembly R C Q) (E F : CanonicalEvaluation I Q C T) : E.value = F.value := by
  have localized_assembly_eq
      (R S : CommRingCat.{0}) (I : DeterminantSources) (g : R ⟶ S)
      (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
      (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
      (T : TermAssembly R C Q) (E F : LocalizedAssembly I g Q C T) :
      E.toTermAssembly = F.toTermAssembly := by
    have h : E.termIso = F.termIso := by
      funext i
      apply Iso.ext
      apply ModuleCat.hom_ext
      apply ((I.terms g C).scalar i (sumTerms S (scalarFamily I g Q) i (subsets m))).injective
      apply LinearMap.ext
      intro x
      exact (E.normalized i x).trans (F.normalized i x).symm
    cases E with
    | mk E he =>
      cases F with
      | mk F hf =>
        cases E
        cases F
        cases h
        rfl
  have localized_comparison_eq
      (R S : CommRingCat.{0}) (I : DeterminantSources) (g : R ⟶ S)
      (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
      (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
      (T : TermAssembly R C Q) (E F : CanonicalEvaluation I Q C T)
      (V : DeterminantScalarTensorModels.ScalarTensorSources g)
      (B : FreeSubsetBases S (scalarFamily I g Q)) :
      localizedComparison I Q C E.comparison V = localizedComparison I Q C F.comparison V := by
    have hv : assembledVector S (I.scalar g C).target (scalarFamily I g Q)
        (E.exact g) (E.assembly g).toTermAssembly B =
        assembledVector S (I.scalar g C).target (scalarFamily I g Q)
          (F.exact g) (F.assembly g).toTermAssembly B := by
      rw [sum_exact_eq S m (scalarFamily I g Q) (E.exact g) (F.exact g),
        localized_assembly_eq R S I g C m Q T (E.assembly g) (F.assembly g)]
    obtain ⟨f, hf⟩ := assembled_tensor_coordinate S (I.scalar g C).target m
      (scalarFamily I g Q) (E.exact g) (E.assembly g).toTermAssembly B
      (degrees S (I.scalar g C).target)
    have := determinantObject_invertible S (I.scalar g C).target
    apply Iso.ext
    apply ModuleCat.hom_ext
    apply maps_eq_on_generator S (determinantObject S (I.scalar g C).target) _
      (assembledVector S (I.scalar g C).target (scalarFamily I g Q)
        (E.exact g) (E.assembly g).toTermAssembly B) f hf
    rw [E.comparison_normalized g V B, hv, F.comparison_normalized g V B]
  have localized_values_eq
      (R S : CommRingCat.{0}) (I : DeterminantSources) (g : R ⟶ S)
      (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
      (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
      (T : TermAssembly R C Q) (E F : CanonicalEvaluation I Q C T)
      (B : FreeSubsetBases S (scalarFamily I g Q))
      (A : AdaptedBases S (I.scalar g C).target) :
      DeterminantScalarTensorModels.vector g (pairingObject R Q) E.value =
        DeterminantScalarTensorModels.vector g (pairingObject R Q) F.value := by
    let V := native_sources R S g
    have ht := (E.torsion_normalized g A).trans (F.torsion_normalized g A).symm
    have hc := localized_comparison_eq R S I g C m Q T E F V B
    apply (scalarPairingComparison I g Q V).toLinearEquiv.injective
    have h := congrArg (fun e ↦ e.hom
      ((I.comparison g C).comparison.hom
        (DeterminantScalarTensorModels.vector g (determinantObject R C) E.torsion))) hc
    have hf : (localizedComparison I Q C F.comparison V).hom
        ((I.comparison g C).comparison.hom
          (DeterminantScalarTensorModels.vector g (determinantObject R C) E.torsion)) =
        (localizedComparison I Q C F.comparison V).hom
          ((I.comparison g C).comparison.hom
            (DeterminantScalarTensorModels.vector g (determinantObject R C) F.torsion)) :=
      congrArg (localizedComparison I Q C F.comparison V).hom ht
    have he := h.trans hf
    simpa [localizedComparison, vector_naturality, CanonicalEvaluation.value] using he
  have cover_values_eq
      (R : CommRingCat.{0}) (I : DeterminantSources)
      (C : BoundedProjectiveDeterminants.Complex R) (m : ℕ)
      (Q : Finset (Fin m) → BoundedProjectiveDeterminants.Complex R)
      (D : EvaluationCover I Q C) (M : ModuleCat.{0} R) (x y : M)
      (h : ∀ c : D.index,
        DeterminantScalarTensorModels.vector (D.map c) M x =
          DeterminantScalarTensorModels.vector (D.map c) M y) : x = y := by
    classical
    by_contra hxy
    have hn : Module.eqIdeal R x y ≠ ⊤ := by
      intro he
      have hh : (1 : R) ∈ Module.eqIdeal R x y := he ▸ Submodule.mem_top
      exact hxy (by simpa [Module.eqIdeal] using hh)
    obtain ⟨P, hP, hle⟩ := (Module.eqIdeal R x y).exists_le_maximal hn
    let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
    obtain ⟨c, q, hq⟩ := D.cover p
    let := D.algebra c
    have := D.localization c
    have he : D.element c ∉ P := by
      intro hp
      have hp' : algebraMap R (D.ring c) (D.element c) ∈ q.asIdeal := by
        rw [← D.map_normalized c]
        change (D.map c).hom (D.element c) ∈ q.asIdeal
        change D.element c ∈ (PrimeSpectrum.comap (D.map c).hom q).asIdeal
        change D.element c ∈ ((Spec.map (D.map c)) q).asIdeal
        rw [hq]
        exact hp
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp'
        (IsLocalization.Away.algebraMap_isUnit (D.element c)))
    have hh := h c
    change (1 : D.ring c) ⊗ₜ[R, (D.map c).hom] x =
      (1 : D.ring c) ⊗ₜ[R, (D.map c).hom] y at hh
    rw [D.map_normalized c] at hh
    have hmod : Module.compHom (D.ring c) (algebraMap R (D.ring c)) =
        (inferInstance : Module R (D.ring c)) := by
      ext r s
      exact (Algebra.smul_def r s).symm
    rw [hmod] at hh
    change (TensorProduct.mk R (D.ring c) M 1) x =
      (TensorProduct.mk R (D.ring c) M 1) y at hh
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (D.element c))
      (TensorProduct.mk R (D.ring c) M 1)).mp hh
    obtain ⟨n, hn⟩ := s.property
    change (D.element c) ^ n = (s : R) at hn
    change (s : R) • x = (s : R) • y at hs
    have hsP : (D.element c) ^ n ∈ P := by
      apply hle
      change (D.element c) ^ n • x = (D.element c) ^ n • y
      rw [hn]
      exact hs
    exact he (hP.isPrime.mem_of_pow_mem n hsP)
  apply cover_values_eq R I C m Q E.freeCover (pairingObject R Q)
  intro c
  exact localized_values_eq R (E.freeCover.ring c) I (E.freeCover.map c) C m Q T E F
    (E.freeCover.subsetBases c) (E.freeCover.adaptedBases c)
end WantedExt.AlgebraicGeometry.CanonicalKoszulDeterminants

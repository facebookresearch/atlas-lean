/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricPositiveAlgebra
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricHarrisonDegreeOne
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection
public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import Mathlib.Algebra.Homology.Single
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjectionSurjective
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Proper-shuffle cotangent augmentation and degree-zero homology

Let k be a commutative ring, A a commutative k-algebra and M a compatible symmetric coefficient
module. Let P be the Hochschild chain quotient by the images of shuffle pairings whose two
degrees are positive. Restrict P along n ↦ n+1 to obtain Ccot, with Ccotₙ = Pₙ₊₁. In degree one
there are no both-positive relations, so the universal-differential map descends to P₁.

The class [m ⊗ a] maps to m ⊗_A da, first as a coefficient one-form and then through
∧¹_AΩ¹_{A/k} ≅ Ω¹_{A/k}. This map kills the incoming proper boundary and defines a chain
augmentation Ccot → (M ⊗_AΩ¹_{A/k})[0], with the coefficient target placed in its canonical
common-universe lift.

The Leibniz boundary presentation and right exactness of coefficient tensoring identify the
augmentation kernel with the incoming boundary range and prove surjectivity. Hence the
coefficient cotangent module is the cokernel of Ccot₁ → Ccot₀, and H₀(Ccot) ≅ M ⊗_AΩ¹_{A/k}. The
forward, inverse, quotient-class and universe-projection formulas are stated explicitly. No
coefficient-flatness or rationality hypothesis is needed for this degree-zero comparison.

For the degree-one proper-shuffle presentation of Harrison homology, see J.-L. Loday, Cyclic
Homology, second edition, §4.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [SMulCommClass k A M]

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. The degreewise quotient projections Cₙ(A,M) = M
⊗[k] A^{⊗n} → Pₙ descend through the both-positive shuffle image submodules and form a chain map
properShuffleProjection : C(A,M) → P. -/
def properShuffleProjection : chainComplex k A M ⟶ positiveQuotient k A M := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  letI : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  letI : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImageProjection (pairing.{u, v, w} k A M)
    (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Restrict the proper quotient P along the positive
natural-number embedding n ↦ n+1. This defines properCotangentComplex, with degree-n term Pₙ₊₁
and consecutive differential inherited from P without an additional sign. -/
abbrev properCotangentComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (positiveQuotient k A M).restriction ComplexShape.positiveNatEmbedding

omit [SMulCommClass k A M] in
/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For every n : ℕ,
(properCotangentComplex k A M).X n equals (positiveQuotient k A M).X (n+1). -/
theorem properCotangentComplex_X (n : ℕ) :
    (properCotangentComplex k A M).X n = (positiveQuotient k A M).X (n + 1) := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. cotangentFormModule is the degree-one term of the
zero-differential coefficient-form complex: the canonical universe lift of M ⊗[A] ∧¹_AΩ¹_{A/k},
regarded as a k-module. -/
abbrev cotangentFormModule : ModuleCat.{max u v w} k :=
  (coefficientDifferentialFormComplex k A M).X 1

omit [SMulCommClass k A M] in
private theorem properRelations_one : rawPositiveRelations k A M 1 = ⊥ := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages_one (pairing.{u, v, w} k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Since the both-positive
relation submodule in degree one is zero, the universal-differential map descends to G : P₁ →
cotangentFormModule. It sends the class [m ⊗ a] to the lifted coefficient one-form m ⊗_A da. -/
def properCotangentDegreeMap : (positiveQuotient k A M).X 1 ⟶ cotangentFormModule k A M :=
  ModuleCat.ofHom ((rawPositiveRelations k A M 1).liftQ
    ((coefficientDifferentialFormChainMap k A M).f 1).hom (by
      rw [properRelations_one]
      exact bot_le))

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. If π : C(A,M) → P is
properShuffleProjection and G is properCotangentDegreeMap, then π.f 1 ≫ G equals the degree-one
component of coefficientDifferentialFormChainMap k A M. -/
theorem properCotangentDegreeMap_projection :
    (properShuffleProjection k A M).f 1 ≫ properCotangentDegreeMap k A M =
      (coefficientDifferentialFormChainMap k A M).f 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

omit [SMulCommClass k A M] in
private theorem properProjection_epi (n : ℕ) : Epi ((properShuffleProjection k A M).f n) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  change Function.Surjective (rawPositiveRelations k A M n).mkQ
  exact Submodule.mkQ_surjective _

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The composite P.d 2 1 ≫
properCotangentDegreeMap k A M is zero. Thus the incoming degree-two proper boundary is
annihilated by the universal differential map. -/
theorem properCotangentDegreeMap_boundary :
    (positiveQuotient k A M).d 2 1 ≫ properCotangentDegreeMap k A M = 0 := by
  let π := properShuffleProjection k A M
  let F := coefficientDifferentialFormChainMap k A M
  let _ : Epi (π.f 2) := properProjection_epi k A M 2
  apply (cancel_epi (π.f 2)).1
  calc
    _ = (π.f 2 ≫ (positiveQuotient k A M).d 2 1) ≫ properCotangentDegreeMap k A M :=
      (Category.assoc _ _ _).symm
    _ = ((chainComplex k A M).d 2 1 ≫ π.f 1) ≫ properCotangentDegreeMap k A M :=
      congrArg (fun h => h ≫ properCotangentDegreeMap k A M) (π.comm 2 1)
    _ = (chainComplex k A M).d 2 1 ≫ F.f 1 :=
      (Category.assoc _ _ _).trans
        (congrArg (fun h => (chainComplex k A M).d 2 1 ≫ h)
          (properCotangentDegreeMap_projection k A M))
    _ = F.f 2 ≫ (coefficientDifferentialFormComplex k A M).d 2 1 := (F.comm 2 1).symm
    _ = 0 := (congrArg (fun d => F.f 2 ≫ d)
      (coefficientDifferentialFormComplex_d_eq_zero k A M 2 1)).trans Limits.comp_zero
    _ = _ := Limits.comp_zero.symm

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The degree-one proper
descent G defines a chain map Ccot → cotangentFormModule[0], where the target is concentrated in
degree zero. Its degree-zero component is G, and G kills Ccot.d 1 0. -/
def properCotangentAugmentation : properCotangentComplex k A M ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (cotangentFormModule k A M) :=
  (ChainComplex.toSingle₀Equiv (properCotangentComplex k A M) (cotangentFormModule k A M)).symm
    ⟨properCotangentDegreeMap k A M, by
      change (positiveQuotient k A M).d 2 1 ≫ properCotangentDegreeMap k A M = 0
      exact properCotangentDegreeMap_boundary k A M⟩

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The degree-zero
component of properCotangentAugmentation k A M equals properCotangentDegreeMap k A M, under
Ccot₀ = P₁. -/
theorem properCotangentAugmentation_f_zero :
    (properCotangentAugmentation k A M).f 0 = properCotangentDegreeMap k A M := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For m ∈ M and a : Fin 1
→ A, properCotangentDegreeMap sends [m ⊗ ⊗ⱼaⱼ] to the canonical lift of m ⊗_A(∧ⱼ daⱼ) in the
coefficient one-form module. -/
theorem properCotangentDegreeMap_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentDegreeMap k A M).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A 1 (fun j => KaehlerDifferential.D k A (a j))) := by
  exact coefficientDifferentialFormChainMap_tprod k A M 1 m a

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. coefficientCotangentModule is the k-module given
by the canonical universe lift of M ⊗[A] Ω¹_{A/k}. The lift places it in the common
coefficient-complex universe. -/
abbrev coefficientCotangentModule : ModuleCat.{max u v w} k :=
  ModuleCat.of k (ULift.{u} (M ⊗[A] KaehlerDifferential k A))

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. The exterior degree-one equivalence ∧¹_AΩ¹_{A/k} ≅
Ω¹_{A/k}, tensored with M and transported through the canonical lifts, gives an isomorphism
cotangentFormModule ≅ coefficientCotangentModule in the category of k-modules. -/
def cotangentFormOneIso : cotangentFormModule k A M ≅ coefficientCotangentModule k A M := by
  let Ω := KaehlerDifferential k A
  let e : M ⊗[A] (⋀[A]^1 Ω) ≃ₗ[k] M ⊗[A] Ω :=
    (TensorProduct.congr (LinearEquiv.refl A M) (exteriorPower.oneEquiv A Ω)).restrictScalars k
  exact ((ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^1 Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^1 Ω)).trans
    (e.trans (ULift.moduleEquiv : ULift.{u} (M ⊗[A] Ω) ≃ₗ[k] M ⊗[A] Ω).symm)).toModuleIso

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Compose
properCotangentAugmentation : Ccot → cotangentFormModule[0] with the degree-zero map induced by
cotangentFormOneIso. This gives a chain map Ccot → coefficientCotangentModule[0] whose
degree-zero value on [m ⊗ a] is the lifted tensor m ⊗_A da. -/
def properShuffleCotangentMap : properCotangentComplex k A M ⟶
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj (coefficientCotangentModule k A M) :=
  properCotangentAugmentation k A M ≫
    (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentFormOneIso k A M).hom

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1.
properShuffleCotangentMap equals properCotangentAugmentation followed by the single-degree-zero
chain map induced by (cotangentFormOneIso k A M).hom. -/
theorem properShuffleCotangentMap_eq :
    properShuffleCotangentMap k A M = properCotangentAugmentation k A M ≫
      (ChainComplex.single₀ (ModuleCat.{max u v w} k)).map (cotangentFormOneIso k A M).hom := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The underlying linear
map properCotangentDegreeMap : P₁ → cotangentFormModule is surjective. Universal differentials
generate Ω¹_{A/k}, and the coefficient tensor presentation preserves this surjectivity. -/
theorem properCotangentDegreeMap_surjective :
    Function.Surjective (properCotangentDegreeMap k A M).hom := by
  intro y
  obtain ⟨x, hx⟩ := coefficientDifferentialFormChainMap_surjective k A M 1 y
  refine ⟨(rawPositiveRelations k A M 1).mkQ x, ?_⟩
  change ((coefficientDifferentialFormChainMap k A M).f 1).hom x = y
  exact hx

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The composite G ≫
cotangentFormOneIso.hom defines properCotangentScalarAugmentation : Ccot₀ →
coefficientCotangentModule. It sends [m ⊗ a] to the canonical lift of m ⊗_A da. -/
def properCotangentScalarAugmentation : (properCotangentComplex k A M).X 0 ⟶
    coefficientCotangentModule k A M :=
  properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The degree-zero scalar
augmentation g satisfies Ccot.d 1 0 ≫ g = 0, where g = properCotangentScalarAugmentation k A M. -/
theorem properCotangentScalarAugmentation_boundary :
    (properCotangentComplex k A M).d 1 0 ≫ properCotangentScalarAugmentation k A M = 0 := by
  change (positiveQuotient k A M).d 2 1 ≫
    (properCotangentDegreeMap k A M ≫ (cotangentFormOneIso k A M).hom) = 0
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (cotangentFormOneIso k A M).hom)
      (properCotangentDegreeMap_boundary k A M)).trans Limits.zero_comp)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1.
properCotangentScalarAugmentation : Ccot₀ → coefficientCotangentModule is surjective. This
follows from the surjective one-form descent and the one-form-to-cotangent isomorphism, without
any flatness condition on M. -/
theorem properCotangentScalarAugmentation_surjective :
    Function.Surjective (properCotangentScalarAugmentation k A M).hom := by
  intro y
  let e := cotangentFormOneIso k A M
  obtain ⟨x, hx⟩ := properCotangentDegreeMap_surjective k A M (e.inv.hom y)
  refine ⟨x, ?_⟩
  change e.hom.hom ((properCotangentDegreeMap k A M).hom x) = y
  exact (congrArg e.hom.hom hx).trans (ConcreteCategory.congr_hom e.inv_hom_id y)

omit [SMulCommClass k A M] in
/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. For m ∈ M and a : Fin 1 → A, cotangentFormOneIso
sends the lift of m ⊗_A ∧ⱼdaⱼ to the lift of m ⊗_A d(a₀). -/
theorem cotangentFormOneIso_tprod (m : M) (a : Fin 1 → A) :
    (cotangentFormOneIso k A M).hom.hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A 1
        (fun j => KaehlerDifferential.D k A (a j)))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  change ULift.up (m ⊗ₜ[A] exteriorPower.oneEquiv A (KaehlerDifferential k A)
      (exteriorPower.ιMulti A 1 (fun j => KaehlerDifferential.D k A (a j)))) = _
  rw [exteriorPower.oneEquiv_ιMulti]

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For m ∈ M and a : Fin 1
→ A, properCotangentScalarAugmentation sends the quotient class of m ⊗ ⊗ⱼaⱼ to the canonical
lift of m ⊗_A d(a₀). -/
theorem properCotangentScalarAugmentation_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentScalarAugmentation k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  change (cotangentFormOneIso k A M).hom.hom
    ((properCotangentDegreeMap k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
  exact (congrArg (cotangentFormOneIso k A M).hom.hom
    (properCotangentDegreeMap_tprod k A M m a)).trans (cotangentFormOneIso_tprod k A M m a)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Since the scalar
augmentation g kills Ccot.d 1 0, it descends through the degree-zero homology cokernel to
properCotangentHomologyZeroMap : H₀(Ccot) → coefficientCotangentModule. -/
def properCotangentHomologyZeroMap : (properCotangentComplex k A M).homology 0 ⟶
    coefficientCotangentModule k A M :=
  (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M)).desc
    (CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
      (properCotangentScalarAugmentation_boundary k A M))

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Let ρ : Ccot₀ →
H₀(Ccot) be homologyZeroClass and h the induced cotangent homology map. Then ρ ≫ h =
properCotangentScalarAugmentation k A M. -/
@[reassoc]
theorem properCotangentHomologyZeroMap_class :
    ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫
      properCotangentHomologyZeroMap k A M = properCotangentScalarAugmentation k A M := by
  exact Cofork.IsColimit.π_desc
    (t := CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
      (properCotangentScalarAugmentation_boundary k A M))
    (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M))

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For m ∈ M and a : Fin 1
→ A, the induced H₀ map sends the homology class of [m ⊗ ⊗ⱼaⱼ] to the canonical lift of m ⊗_A
d(a₀). -/
theorem properCotangentHomologyZeroMap_tprod (m : M) (a : Fin 1 → A) :
    (properCotangentHomologyZeroMap k A M).hom
      ((ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      ULift.up (m ⊗ₜ[A] KaehlerDifferential.D k A (a 0)) := by
  have h := ConcreteCategory.congr_hom (properCotangentHomologyZeroMap_class k A M)
    ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  exact h.trans (properCotangentScalarAugmentation_tprod k A M m a)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Every element of
coefficientCotangentModule is the image of a degree-zero class under
properCotangentHomologyZeroMap. This is the surjectivity of the scalar augmentation after
passage to the incoming-boundary cokernel. -/
theorem properCotangentHomologyZeroMap_surjective :
    Function.Surjective (properCotangentHomologyZeroMap k A M).hom := by
  intro y
  obtain ⟨x, hx⟩ := properCotangentScalarAugmentation_surjective k A M y
  refine ⟨(ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom x, ?_⟩
  have h := ConcreteCategory.congr_hom (properCotangentHomologyZeroMap_class k A M) x
  exact h.trans hx

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1.
properCotangentHomologyZeroMap : H₀(Ccot) → coefficientCotangentModule is an epimorphism in the
category of k-modules, because its underlying linear map is surjective. -/
theorem properCotangentHomologyZeroMap_epi : Epi (properCotangentHomologyZeroMap k A M) :=
  (ModuleCat.epi_iff_surjective _).mpr (properCotangentHomologyZeroMap_surjective k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For every x ∈ M ⊗[k]
A^{⊗1}, the scalar augmentation of its proper quotient class is the canonical lift of
algebraOneToKaehler k A M x. This A-linear presentation sends m ⊗ a to m ⊗_A da. -/
theorem properCotangentScalarAugmentation_mkQ (x : M ⊗[k] TensorPower k 1 A) :
    (properCotangentScalarAugmentation k A M).hom ((rawPositiveRelations k A M 1).mkQ x) =
      ULift.up (algebraOneToKaehler k A M x) := by
  let l : (M ⊗[k] TensorPower k 1 A) →ₗ[k] ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
    ((properShuffleProjection k A M).f 1 ≫ properCotangentScalarAugmentation k A M).hom
  let r : (M ⊗[k] TensorPower k 1 A) →ₗ[k] ULift.{u} (M ⊗[A] KaehlerDifferential k A) :=
    (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[k]
      M ⊗[A] KaehlerDifferential k A).symm.toLinearMap.comp
        ((algebraOneToKaehler k A M).restrictScalars k)
  have h : l = r := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change (properCotangentScalarAugmentation k A M).hom
      ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
        ULift.up (algebraOneToKaehler k A M (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    exact (properCotangentScalarAugmentation_tprod k A M m a).trans
      (congrArg ULift.up (algebraOneToKaehler_tprod k A M m a)).symm
  exact DFunLike.congr_fun h x

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The sequence Ccot₁ →
Ccot₀ → coefficientCotangentModule, with arrows Ccot.d 1 0 and
properCotangentScalarAugmentation, is exact. Equivalently g(y)=0 if and only if y=d(x) for some
x ∈ Ccot₁. The universal derivation and right-exact coefficient tensor presentation prove this
without coefficient flatness. -/
theorem properCotangentScalarAugmentation_exact :
    Function.Exact ((properCotangentComplex k A M).d 1 0).hom
      (properCotangentScalarAugmentation k A M).hom := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (rawPositiveRelations k A M 1) y
  constructor
  · intro hx
    have hx' : algebraOneToKaehler k A M x = 0 := by
      have h : ULift.up (algebraOneToKaehler k A M x) =
          (0 : ULift.{u} (M ⊗[A] KaehlerDifferential k A)) :=
        (properCotangentScalarAugmentation_mkQ k A M x).symm.trans hx
      exact congrArg ULift.down h
    obtain ⟨z, hz⟩ := (algebraBoundary_two_exact k A M x).mp hx'
    refine ⟨(rawPositiveRelations k A M 2).mkQ z, ?_⟩
    change ((positiveQuotient k A M).d 2 1).hom
      ((rawPositiveRelations k A M 2).mkQ z) = (rawPositiveRelations k A M 1).mkQ x
    exact (positiveQuotient_d_mk k A M 1 z).trans
      (congrArg (rawPositiveRelations k A M 1).mkQ hz)
  · rintro ⟨z, hz⟩
    rw [← hz]
    exact ConcreteCategory.congr_hom (properCotangentScalarAugmentation_boundary k A M) z

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The kernel of the
underlying linear map properCotangentScalarAugmentation equals the range of
(properCotangentComplex k A M).d 1 0. This is the Leibniz boundary presentation of coefficient
cotangents. -/
theorem properCotangentScalarAugmentation_kernel :
    LinearMap.ker (properCotangentScalarAugmentation k A M).hom =
      LinearMap.range ((properCotangentComplex k A M).d 1 0).hom := by
  ext x
  exact properCotangentScalarAugmentation_exact k A M x

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1.
properCotangentCokernelCofork is the cofork of Ccot.d 1 0 with point coefficientCotangentModule
and projection properCotangentScalarAugmentation. The cofork equation is d ≫ g = 0. -/
def properCotangentCokernelCofork : CokernelCofork ((properCotangentComplex k A M).d 1 0) :=
  CokernelCofork.ofπ (properCotangentScalarAugmentation k A M)
    (properCotangentScalarAugmentation_boundary k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The cofork with
projection properCotangentScalarAugmentation is a cokernel of Ccot.d 1 0 in the category of
k-modules. Exactness identifies its kernel with the boundary range, and surjectivity supplies
the cokernel universal property. -/
def properCotangentCokernelIsColimit : IsColimit (properCotangentCokernelCofork k A M) :=
  ModuleCat.isColimitCokernelCofork ((properCotangentComplex k A M).d 1 0)
    (properCotangentScalarAugmentation k A M)
    (properCotangentScalarAugmentation_exact k A M)
    (properCotangentScalarAugmentation_surjective k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Cokernel uniqueness
gives an isomorphism H₀(Ccot) ≅ coefficientCotangentModule. Its forward map is the induced
scalar augmentation and is constructed over arbitrary commutative k and A. -/
def properCotangentHomologyZeroIso : (properCotangentComplex k A M).homology 0 ≅
    coefficientCotangentModule k A M :=
  (ChainComplex.homologyZeroCoforkIsColimit (properCotangentComplex k A M)).coconePointUniqueUpToIso
    (properCotangentCokernelIsColimit k A M)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The forward map of
properCotangentHomologyZeroIso k A M equals properCotangentHomologyZeroMap k A M. -/
theorem properCotangentHomologyZeroIso_hom :
    (properCotangentHomologyZeroIso k A M).hom = properCotangentHomologyZeroMap k A M := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The inverse of
properCotangentHomologyZeroIso is the unique descent from the cotangent cokernel cofork to the
degree-zero homology cofork. It is characterized by g ≫ h⁻¹ = ρ, with g the scalar augmentation
and ρ : Ccot₀ → H₀(Ccot) the class map. -/
theorem properCotangentHomologyZeroIso_inv :
    (properCotangentHomologyZeroIso k A M).inv =
      (properCotangentCokernelIsColimit k A M).desc
        (ChainComplex.homologyZeroCofork (properCotangentComplex k A M)) := rfl

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Let g : Ccot₀ →
coefficientCotangentModule be the scalar augmentation and h the degree-zero cotangent homology
isomorphism. Then g ≫ h.inv = homologyZeroClass : Ccot₀ → H₀(Ccot). -/
@[reassoc]
theorem properCotangentHomologyZeroIso_class_inv :
    properCotangentScalarAugmentation k A M ≫ (properCotangentHomologyZeroIso k A M).inv =
      ChainComplex.homologyZeroClass (properCotangentComplex k A M) := by
  let e := properCotangentHomologyZeroIso k A M
  have h : ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫ e.hom =
      properCotangentScalarAugmentation k A M := properCotangentHomologyZeroMap_class k A M
  calc
    _ = (ChainComplex.homologyZeroClass (properCotangentComplex k A M) ≫ e.hom) ≫ e.inv :=
      congrArg (fun f => f ≫ e.inv) h.symm
    _ = ChainComplex.homologyZeroClass (properCotangentComplex k A M) := by
      rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. The underlying linear
map of properCotangentHomologyZeroMap is injective, since it is the forward map of the
isomorphism obtained from the Leibniz cokernel presentation. -/
theorem properCotangentHomologyZeroMap_injective :
    Function.Injective (properCotangentHomologyZeroMap k A M).hom := by
  rw [← properCotangentHomologyZeroIso_hom]
  exact (properCotangentHomologyZeroIso k A M).toLinearEquiv.injective

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. Projecting the
canonical universe lift from properCotangentHomologyZeroIso gives a k-linear equivalence
H₀(Ccot) ≃ M ⊗[A] Ω¹_{A/k}. -/
def properCotangentHomologyZeroEquiv :
    (properCotangentComplex k A M).homology 0 ≃ₗ[k] M ⊗[A] KaehlerDifferential k A :=
  (properCotangentHomologyZeroIso k A M).toLinearEquiv.trans
    (ULift.moduleEquiv : ULift.{u} (M ⊗[A] KaehlerDifferential k A) ≃ₗ[k]
      M ⊗[A] KaehlerDifferential k A)

/-- Let k be a commutative ring, A a commutative k-algebra and M an A-module with compatible
k-action, regarded as a symmetric A-bimodule. Let P be the quotient of Hochschild chains by
both-positive shuffle relations, and Ccot its restriction along n ↦ n+1. For m ∈ M and a : Fin 1
→ A, properCotangentHomologyZeroEquiv sends the degree-zero homology class of [m ⊗ ⊗ⱼaⱼ] to m
⊗_A d(a₀). -/
theorem properCotangentHomologyZeroEquiv_tprod (m : M) (a : Fin 1 → A) :
    properCotangentHomologyZeroEquiv k A M
      ((ChainComplex.homologyZeroClass (properCotangentComplex k A M)).hom
        ((rawPositiveRelations k A M 1).mkQ (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      m ⊗ₜ[A] KaehlerDifferential.D k A (a 0) := by
  exact congrArg ULift.down (properCotangentHomologyZeroMap_tprod k A M m a)

end ModuleCat.Algebra.Hochschild.Symmetric

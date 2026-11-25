/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.AdjointCoinvariants
public import MathlibExt.CategoryTheory.Monoidal.ComonObjEpi
public import MathlibExt.Algebra.Homology.TensorHomFunctoriality

/-!
# Coalgebra structure on adjoint Chevalley–Eilenberg coinvariants

The adjoint chain action is a coderivation with zero counit. The coproduct and
counit therefore descend through the coinvariant projection. Their descended
maps satisfy the comonoid laws, and the coaugmentation descends as well.
The coinvariant complex and its projection are bundled as a coalgebra and a
coalgebra morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type u} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)


/-- The canonical tensor data used by the coinvariant complexes. -/
local instance coinvariantTensorStructure : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
/-- The canonical monoidal laws on the original coefficient category. -/
local instance coinvariantMonoidalCategory : MonoidalCategory (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
local instance coinvariantMonoidalPreadditive : MonoidalPreadditive (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
local instance coinvariantMonoidalLinear : MonoidalLinear R (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
local instance adjointCoinvariantFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)
/-- Closedness of the canonical coefficient tensor product. -/
local instance adjointCoinvariantClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)
/-- The native tensor-unit comonoid at the original coefficient height. -/
local instance adjointCoinvariantUnitComon : ComonObj (nativeUnitComplex.{u,v} R) :=
  ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} R) ℕ)
/-- The native CE comonoid before taking coinvariants. -/
local instance canonicalComon : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L

private theorem scalarAction_quotient_comul (s : S) :
    degreeAdjointChainMap R L (ι s) ≫ nativeComplexComul R L ≫
        HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι) (adjointCoinvariantProjection R L ι) = 0 := by
  let K := (canonicalChainData R L).complex
  let Q := adjointCoinvariantComplex R L ι
  let q : K ⟶ Q := adjointCoinvariantProjection R L ι
  let a : K ⟶ K := degreeAdjointChainMap R L (ι s)
  let Δ : K ⟶ K ⊗ K := nativeComplexComul R L
  have hΔ : a ≫ Δ = Δ ≫ ((a ⊗ₘ 𝟙 K) + (𝟙 K ⊗ₘ a)) :=
    degreeAdjointChainMap_comul R L (ι s)
  have hq : a ≫ q = 0 := degreeAdjointChainMap_projection R L ι s
  have hR : (a ⊗ₘ 𝟙 K) ≫ (q ⊗ₘ q) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, hq, Category.id_comp]
    exact HomologicalComplex.zero_tensorHom q
  have hL : (𝟙 K ⊗ₘ a) ≫ (q ⊗ₘ q) = 0 := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, hq, Category.id_comp]
    exact HomologicalComplex.tensorHom_zero q
  have hSum : ((a ⊗ₘ 𝟙 K) + (𝟙 K ⊗ₘ a)) ≫ (q ⊗ₘ q) = 0 := by
    rw [Preadditive.add_comp, hR, hL, add_zero]
  have h₁ := (Category.assoc a Δ (q ⊗ₘ q)).symm
  have h₂ := congrArg (fun z => z ≫ (q ⊗ₘ q)) hΔ
  have h₃ := Category.assoc Δ ((a ⊗ₘ 𝟙 K) + (𝟙 K ⊗ₘ a)) (q ⊗ₘ q)
  have h₄ := congrArg (fun z => Δ ≫ z) hSum
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans comp_zero)))

private theorem actionChain_quotient_comul :
    adjointActionChainMap R L ι ≫
        (nativeComplexComul R L ≫ HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι)
          (adjointCoinvariantProjection R L ι)) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  let t := nativeComplexComul R L ≫ HomologicalComplex.tensorHom
    (adjointCoinvariantProjection R L ι) (adjointCoinvariantProjection R L ι)
  have hF := adjointScalarChainMap_action R L ι s
  have h := congrArg (fun g => (g.f n).hom a)
    ((congrArg (fun g => g ≫ t) hF).trans (scalarAction_quotient_comul R L ι s))
  change (t.f n).hom ((adjointActionLinear R L ι n) (s ⊗ₜ[R] a)) = 0
  exact h

private theorem actionChain_counit :
    adjointActionChainMap R L ι ≫ nativeComplexCounit R L = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro s a
  have hF := adjointScalarChainMap_action R L ι s
  have h := congrArg (fun g => (g.f n).hom a)
    ((congrArg (fun g => g ≫ nativeComplexCounit R L) hF).trans
      (degreeAdjointChainMap_counit R L (ι s)))
  change ((nativeComplexCounit R L).f n).hom
    ((adjointActionLinear R L ι n) (s ⊗ₜ[R] a)) = 0
  exact h

/-- The quotient coproduct is a native cokernel descent of the CE coproduct. -/
def adjointCoinvariantComul : (adjointCoinvariantComplex R L ι) ⟶ (adjointCoinvariantComplex R L ι) ⊗
  (adjointCoinvariantComplex R L ι) :=
  cokernel.desc (adjointActionChainMap R L ι)
    (nativeComplexComul R L ≫ HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι)
      (adjointCoinvariantProjection R L ι))
    (by
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s a
      let t := nativeComplexComul R L ≫ HomologicalComplex.tensorHom
        (adjointCoinvariantProjection R L ι) (adjointCoinvariantProjection R L ι)
      have hF := adjointScalarChainMap_action R L ι s
      have h := congrArg (fun g => (g.f n).hom a)
        ((congrArg (fun g => g ≫ t) hF).trans (scalarAction_quotient_comul R L ι s))
      change (t.f n).hom ((adjointActionLinear R L ι n) (s ⊗ₜ[R] a)) = 0
      exact h)

/-- The quotient counit is a native cokernel descent of the CE counit. -/
def adjointCoinvariantCounit : (adjointCoinvariantComplex R L ι) ⟶ nativeUnitComplex.{u,v} R :=
  cokernel.desc (adjointActionChainMap R L ι) (nativeComplexCounit R L)
    (by
      apply HomologicalComplex.hom_ext
      intro n
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s a
      have hF := adjointScalarChainMap_action R L ι s
      have h := congrArg (fun g => (g.f n).hom a)
        ((congrArg (fun g => g ≫ nativeComplexCounit R L) hF).trans
          (degreeAdjointChainMap_counit R L (ι s)))
      change ((nativeComplexCounit R L).f n).hom
        ((adjointActionLinear R L ι n) (s ⊗ₜ[R] a)) = 0
      exact h)

@[reassoc]
theorem adjointCoinvariantComul_projection :
    (adjointCoinvariantProjection R L ι) ≫ adjointCoinvariantComul R L ι = nativeComplexComul R L ≫
      HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι) (adjointCoinvariantProjection R L ι) :=
  cokernel.π_desc _ _ _

@[reassoc]
theorem adjointCoinvariantCounit_projection :
    (adjointCoinvariantProjection R L ι) ≫ adjointCoinvariantCounit R L ι = nativeComplexCounit R L :=
  cokernel.π_desc _ _ _

/-- The quotient carries a lawful native comonoid, through its epic projection. -/
def adjointCoinvariantComonObj : ComonObj (adjointCoinvariantComplex R L ι) :=
  ComonObj.ofEpi (adjointCoinvariantProjection R L ι) (adjointCoinvariantComul R L ι) (adjointCoinvariantCounit R L ι)
    (adjointCoinvariantComul_projection R L ι) (adjointCoinvariantCounit_projection R L ι)

/-- The coaugmentation of the coinvariant coalgebra. -/
def adjointCoinvariantCoaug : nativeUnitComplex.{u,v} R ⟶ (adjointCoinvariantComplex R L ι) := nativeComplexCoaug R L
  ≫ (adjointCoinvariantProjection R L ι)

theorem adjointCoinvariantCoaug_counit :
    adjointCoinvariantCoaug R L ι ≫ adjointCoinvariantCounit R L ι = 𝟙 _ := by
  rw [adjointCoinvariantCoaug, Category.assoc, adjointCoinvariantCounit_projection,
    nativeComplexCoaug_counit]

theorem adjointCoinvariantCoaug_comul :
    adjointCoinvariantCoaug R L ι ≫ adjointCoinvariantComul R L ι =
      (HomologicalComplex.leftUnitor (nativeUnitComplex.{u,v} R)).inv ≫
        HomologicalComplex.tensorHom (adjointCoinvariantCoaug R L ι)
          (adjointCoinvariantCoaug R L ι) := by
  let K := (canonicalChainData R L).complex
  let Q := adjointCoinvariantComplex R L ι
  let q : K ⟶ Q := adjointCoinvariantProjection R L ι
  let η : nativeUnitComplex.{u,v} R ⟶ K := nativeComplexCoaug R L
  let Δ : K ⟶ K ⊗ K := nativeComplexComul R L
  let unitorMap := (HomologicalComplex.leftUnitor (nativeUnitComplex.{u,v} R)).inv
  have hq : q ≫ adjointCoinvariantComul R L ι = Δ ≫ HomologicalComplex.tensorHom q q :=
    adjointCoinvariantComul_projection R L ι
  have hη : η ≫ Δ = unitorMap ≫ HomologicalComplex.tensorHom η η := nativeComplexCoaug_comul R L
  have ht : HomologicalComplex.tensorHom η η ≫ HomologicalComplex.tensorHom q q =
      HomologicalComplex.tensorHom (η ≫ q) (η ≫ q) :=
    HomologicalComplex.tensorHom_comp_tensorHom η q η q
  have h₁ := Category.assoc η q (adjointCoinvariantComul R L ι)
  have h₂ := congrArg (fun t => η ≫ t) hq
  have h₃ := (Category.assoc η Δ (HomologicalComplex.tensorHom q q)).symm
  have h₄ := congrArg (fun t => t ≫ HomologicalComplex.tensorHom q q) hη
  have h₅ := Category.assoc unitorMap (HomologicalComplex.tensorHom η η) (HomologicalComplex.tensorHom q q)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (congrArg (fun t => unitorMap ≫ t) ht)))))

/-- The coinvariant projection is a native comonoid homomorphism. -/
def adjointCoinvariantProjectionIsComonHom :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    IsComonHom (adjointCoinvariantProjection R L ι) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  exact ⟨adjointCoinvariantCounit_projection R L ι, adjointCoinvariantComul_projection R L ι⟩

/-- The descended coaugmentation is a native comonoid morphism. -/
def adjointCoinvariantCoaugIsComonHom :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    IsComonHom (adjointCoinvariantCoaug R L ι) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  exact ⟨adjointCoinvariantCoaug_counit R L ι, adjointCoinvariantCoaug_comul R L ι⟩

/-- The coinvariant complex bundled with its native comonoid. -/
def adjointCoinvariantCoalgebra : Comon (ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  { X := adjointCoinvariantComplex R L ι, comon := adjointCoinvariantComonObj R L ι }

/-- The projection bundled as a native coalgebra morphism. -/
def adjointCoinvariantCoalgebraProjection : nativeCoalgebra R L ⟶ adjointCoinvariantCoalgebra R L ι := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  letI : IsComonHom (adjointCoinvariantProjection R L ι) := adjointCoinvariantProjectionIsComonHom R L ι
  refine { hom := adjointCoinvariantProjection R L ι, isComonHom_hom := ?_ }
  exact adjointCoinvariantProjectionIsComonHom R L ι

end ChevalleyEilenberg

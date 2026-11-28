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
# The coalgebra of adjoint exterior coinvariants

Let R:Type u be commutative, L:Type v an R-Lie algebra, and
ι:S→L a Lie map with S:Type u. The exterior Chevalley–Eilenberg
complex C has its primitive coproduct Δ and counit ε.
Each adjoint chain action satisfies
Δ A_s=(A_s⊗id+id⊗A_s)Δ and ε A_s=0.

For the coinvariant projection q:C→Q, the maps (q⊗q)Δ and ε
therefore descend to Δ_Q:Q→Q⊗Q and ε_Q:Q→𝟙.
They satisfy coassociativity and the counit laws. The coaugmentation
is q after the exterior coaugmentation, and q is a coalgebra morphism.

The coalgebras are comonoid objects in nonnegative R-module chain
complexes with the signed tensor product. Their carrier height is
max{u,v}; the tensor unit is ULift.{v} R in degree zero.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]
variable {S : Type u} [LieRing S] [LieAlgebra R S] (ι : S →ₗ⁅R⁆ L)


/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
The tensor associator regroups pure tensors, and the unitors
use the down scalar of ULift R. -/
local instance coinvariantTensorStructure : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
The associator and unitors satisfy the monoidal coherence laws,
so these tensor objects define a monoidal module category. -/
local instance coinvariantMonoidalCategory : MonoidalCategory (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
local instance coinvariantMonoidalPreadditive : MonoidalPreadditive (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
local instance coinvariantMonoidalLinear : MonoidalLinear R (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
local instance adjointCoinvariantFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)
/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
Tensoring with an R-module has the R-linear Hom module as its
right adjoint. This gives the closed monoidal structure. -/
local instance adjointCoinvariantClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)
/-- For a commutative ring R:Type u and any universe v, the category
ModuleCat.{max u v} R has tensor product M⊗_R N and unit ULift.{v} R.
The unit chain complex, concentrated in degree zero, has its
canonical comonoid structure with unit coproduct and identity counit. -/
local instance adjointCoinvariantUnitComon : ComonObj (nativeUnitComplex.{u,v} R) :=
  ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} R) ℕ)
/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
The exterior chain complex C has its primitive comonoid:
Δ(x)=1⊗x+x⊗1 on generators, with the degree-zero counit. -/
local instance canonicalComon : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L

private theorem scalarAction_quotient_comul (s : S) :
    degreeAdjointChainMap R L (ι s) ≫ nativeComplexComul R L ≫
        HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι)
          (adjointCoinvariantProjection R L ι) = 0 := by
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

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The coproduct Δ_Q:Q→Q⊗Q is determined by
Δ_Q q=(q⊗q)Δ_C, where Δ_C is the exterior primitive coproduct. -/
def adjointCoinvariantComul : (adjointCoinvariantComplex R L ι) ⟶ (adjointCoinvariantComplex R L
  ι) ⊗
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

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The counit ε_Q:Q→𝟙 is determined by ε_Q q=ε_C,
where ε_C is the exterior chain counit. -/
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
      HomologicalComplex.tensorHom (adjointCoinvariantProjection R L ι)
        (adjointCoinvariantProjection R L ι) :=
  cokernel.π_desc _ _ _

@[reassoc]
theorem adjointCoinvariantCounit_projection :
    (adjointCoinvariantProjection R L ι) ≫ adjointCoinvariantCounit R L ι = nativeComplexCounit R
      L :=
  cokernel.π_desc _ _ _

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The descended coproduct and counit make Q a comonoid in the
signed tensor category of nonnegative R-module complexes. -/
def adjointCoinvariantComonObj : ComonObj (adjointCoinvariantComplex R L ι) :=
  ComonObj.ofEpi (adjointCoinvariantProjection R L ι) (adjointCoinvariantComul R L ι)
    (adjointCoinvariantCounit R L ι)
    (adjointCoinvariantComul_projection R L ι) (adjointCoinvariantCounit_projection R L ι)

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The coaugmentation of Q is u_Q=q u_C:𝟙→Q,
where u_C is the exterior-chain coaugmentation. -/
def adjointCoinvariantCoaug : nativeUnitComplex.{u,v} R ⟶ (adjointCoinvariantComplex R L ι) :=
  nativeComplexCoaug R L
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
  have h₅ := Category.assoc unitorMap (HomologicalComplex.tensorHom η η)
    (HomologicalComplex.tensorHom q q)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (congrArg (fun t => unitorMap ≫ t) ht)))))

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The projection q preserves the coproduct and counit:
Δ_Q q=(q⊗q)Δ_C and ε_Q q=ε_C. Thus it is a comonoid morphism. -/
def adjointCoinvariantProjectionIsComonHom :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    IsComonHom (adjointCoinvariantProjection R L ι) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  exact ⟨adjointCoinvariantCounit_projection R L ι, adjointCoinvariantComul_projection R L ι⟩

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The descended coaugmentation u_Q:𝟙→Q is a comonoid morphism,
preserving the tensor-unit coproduct and counit. -/
def adjointCoinvariantCoaugIsComonHom :
    letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
    IsComonHom (adjointCoinvariantCoaug R L ι) := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  exact ⟨adjointCoinvariantCoaug_counit R L ι, adjointCoinvariantCoaug_comul R L ι⟩

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The complex Q with its descended coproduct and counit is the
bundled coalgebra object in ChainComplex(ModuleCat R,ℕ). -/
def adjointCoinvariantCoalgebra : Comon (ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  { X := adjointCoinvariantComplex R L ι, comon := adjointCoinvariantComonObj R L ι }

/-- Let R:Type u be a commutative ring, L:Type v an R-Lie algebra,
S:Type u another R-Lie algebra, and ι:S→L a Lie homomorphism.
Write C_n=Λ_R^nL and A_s for the degreewise adjoint action of ι(s).
Let Q=C/⟨A_s(z)⟩ be the adjoint coinvariant chain complex and
q:C→Q its projection.
The projection q:C→Q is the bundled morphism from the exterior
Chevalley–Eilenberg coalgebra to its adjoint coinvariant coalgebra. -/
def adjointCoinvariantCoalgebraProjection : nativeCoalgebra R L ⟶ adjointCoinvariantCoalgebra R L
  ι := by
  letI : ComonObj (adjointCoinvariantComplex R L ι) := adjointCoinvariantComonObj R L ι
  letI : IsComonHom (adjointCoinvariantProjection R L ι) := adjointCoinvariantProjectionIsComonHom
    R L ι
  refine { hom := adjointCoinvariantProjection R L ι, isComonHom_hom := ?_ }
  exact adjointCoinvariantProjectionIsComonHom R L ι

end ChevalleyEilenberg

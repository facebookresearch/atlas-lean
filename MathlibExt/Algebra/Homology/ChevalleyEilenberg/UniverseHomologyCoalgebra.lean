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

public import MathlibExt.Algebra.Homology.UniverseKunneth.Coalgebra
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.PrimitiveFree

/-!
# CE homology coalgebras over independently sized fields and Lie carriers

Over a field k, the canonical CE comonoid and the Künneth monoidal homology functor give a
coaugmented graded cocommutative coalgebra on H_*(L). The scalar field and Lie carrier have
separate universes u and v; the common module category has height max u v.

Lie homomorphisms in the common Lie carrier universe induce comonoid maps on graded homology.
The chain primitive equation agrees with the CE primitive map at the same lifted unit.
Homology of its kernel has a canonical comparison to the primitive kernel in the homology
coalgebra, characterized by its composite with the kernel inclusion.

For a free Lie module, H₁ of the primitive complex identifies with the lifted Lie carrier.
This is a primitive-complex homology isomorphism, distinct from asserting that the comparison
to primitives in CE homology is an isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ComonObj

namespace ChevalleyEilenberg.UniverseHomologyCoalgebra

variable (k : Type u) [Field k]
variable (L : Type v) [LieRing L] [LieAlgebra k L]

open scoped ModuleCat.UniverseTensor

local instance : HasFiniteBiproducts (ModuleCat.{max u v} k) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} k)

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. The canonical tensor structure on ModuleCat.{max u v} k is monoidal closed. -/
local instance originalFieldHomologyClosed : MonoidalClosed (ModuleCat.{max u v} k) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := k)

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. The local ComonObj C is nativeComonObj k L, with the CE coproduct and
counit. -/
local instance originalFieldChainComon : ComonObj ((canonicalChainData k L).complex : ChainComplex
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) := nativeComonObj k L






local instance : HasFiniteBiproducts (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) :=
  CategoryTheory.Abelian.hasFiniteBiproducts
    (C := ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. nativeUnitComplex k has the canonical ComonObj structure of the chain tensor
unit in the common module-category height. -/
local instance chainUnitNative : ComonObj (nativeUnitComplex.{u,v} k) :=
  ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} k) ℕ)

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. The comonoid on C in ChainComplex
(ModuleCat.UniverseScalarRestriction.Modules k) ℕ is nativeComonObj k L. -/
local instance chainComonoid :
    let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
      (canonicalChainData k L).complex
    ComonObj C := nativeComonObj k L
/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. The object 𝟙_ of the chain category has the tensor-unit ComonObj structure,
with unit-induced coproduct and identity counit. -/
local instance chainUnitComonoid : ComonObj (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)
  ℕ)) := ComonObj.instTensorUnit _
local instance actualCoaugmentation : IsComonHom (nativeComplexCoaug k L) := nativeComplexCoaugIsComonHom k L

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. homologyComonObj is the ComonObj structure on H(C) induced from
nativeComonObj by the field Künneth monoidal functor. -/
def homologyComonObj : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) := by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  exact HomologicalComplex.UniverseKunneth.comonObj.{u,v} C

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. homologyCoaug maps the tensor unit of GradedObject ℕ Modules to H(C),
obtained from nativeComplexCoaug and the monoidal homology unit comparison. -/
def homologyCoaug : 𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)) ⟶
  (HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k L).complex :
    ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) :=
  HomologicalComplex.UniverseKunneth.coaug.{u,v} ((canonicalChainData k L).complex : ChainComplex
    (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) (nativeComplexCoaug k L)

theorem homologyCoaugIsComonHom :
    letI : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) :=
      homologyComonObj k L
    letI : ComonObj (𝟙_ (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))) :=
      ComonObj.instTensorUnit (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k))
    IsComonHom (homologyCoaug k L) :=
  by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C :=
    nativeComplexCoaug k L
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k L
  exact HomologicalComplex.UniverseKunneth.coaugIsComonHom.{u,v} C η

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. homologyPointedComon is the object under the trivial graded comonoid with
carrier H(C) and coaugmentation homologyCoaug. -/
def homologyPointedComon : Under (Comon.trivial (GradedObject ℕ (ModuleCat.UniverseScalarRestriction.Modules.{u,v}
  k))) :=
by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C :=
    nativeComplexCoaug k L
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k L
  exact HomologicalComplex.UniverseKunneth.coaugmented.{u,v} C η

@[reassoc]
theorem homologyComul_canonical :
    letI : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) :=
      homologyComonObj k L
    Δ[(HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k L).complex :
      ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)] ≫
        HomologicalComplex.UniverseKunneth.tensorator.{u,v} ((canonicalChainData k L).complex : ChainComplex
          (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ((canonicalChainData k L).complex : ChainComplex
            (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) =
      (HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).map (nativeComplexComul k L) :=
by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  exact HomologicalComplex.UniverseKunneth.comul_tensorator.{u,v} C

theorem homology_cocommutative :
    letI : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) :=
      homologyComonObj k L
    Δ[(HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k L).complex :
      ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)] ≫
        (HomologicalComplex.UniverseKunneth.koszulSwap.{u,v}
          ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k L).complex :
            ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))
              ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k
                L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ))).hom =
                  Δ[(HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k
                    L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)] :=
by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  exact HomologicalComplex.UniverseKunneth.comul_cocommutative.{u,v} C (nativeComplexComul_cocommutative k L)

variable {L' : Type v} [LieRing L'] [LieAlgebra k L']

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. For L' : Type v and f : L →ₗ⁅k⁆ L', H(nativeComplexMap f) is a comonoid
morphism between homologyComonObj k L and homologyComonObj k L'. -/
theorem homologyMapIsComonHom (f : L →ₗ⁅k⁆ L') :
    letI : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) :=
      homologyComonObj k L
    letI : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj ((canonicalChainData k
      L').complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) := homologyComonObj k L'
    IsComonHom ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).map (nativeComplexMap k L f)) := by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  let D : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L').complex
  let g : C ⟶ D := nativeComplexMap k L f
  let H := HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)
  letI : H.Monoidal := HomologicalComplex.UniverseKunneth.monoidalOfField.{u,v}
  letI : ComonObj C := nativeComonObj k L
  letI : ComonObj D := nativeComonObj k L'
  letI : IsComonHom g := nativeComplexMapIsComonHom k L f
  exact Functor.map.instIsComon_Hom H g

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. The primitive equation attached to C and nativeComplexCoaug equals
nativePrimitiveMap k L, using the same chain tensor unit and coaugmentation. -/
theorem primitiveEquation_eq_native :
    HomologicalComplex.UniverseKunneth.primitiveEquation.{u,v} ((canonicalChainData k L).complex : ChainComplex
      (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) (nativeComplexCoaug k L) =
      nativePrimitiveMap k L := rfl

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. primitiveHomologyComparison : H(nativePrimitiveComplex k L) ⟶
ker(homologyPrimitiveEquation C) is the canonical primitive-kernel comparison. Composing it
with the kernel inclusion gives the homology map of the primitive chain inclusion. -/
def primitiveHomologyComparison :
    (HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj (nativePrimitiveComplex k L) ⟶
      kernel (HomologicalComplex.UniverseKunneth.homologyPrimitiveEquation.{u,v} ((canonicalChainData k L).complex :
        ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) (nativeComplexCoaug k L)) :=
by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C :=
    nativeComplexCoaug k L
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k L
  exact HomologicalComplex.UniverseKunneth.primitiveComparison.{u,v} C η

@[reassoc (attr := simp)]
theorem primitiveHomologyComparison_inclusion :
    primitiveHomologyComparison k L ≫
      kernel.ι (HomologicalComplex.UniverseKunneth.homologyPrimitiveEquation.{u,v} ((canonicalChainData k L).complex :
        ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) (nativeComplexCoaug k L)) =
      (HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).map (nativePrimitiveInclusion k L) :=
by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  let η : 𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) ⟶ C :=
    nativeComplexCoaug k L
  letI : IsComonHom η := nativeComplexCoaugIsComonHom k L
  exact HomologicalComplex.UniverseKunneth.primitiveComparison_ι.{u,v} C η

/-- Let k : Type u be a field and L : Type v a k-Lie algebra. Put C = (canonicalChainData k
L).complex in ModuleCat.{max u v} k and H(C) its graded homology under the field Künneth
monoidal functor. If Module.Free k L holds, primitiveHomologyOneIso identifies
(nativePrimitiveComplex k L).homology 1 with ModuleCat.of k (ULift.{u} L), by the
primitive-singleton chain isomorphism and its degree-one homology. -/
def primitiveHomologyOneIso [Module.Free k L] :
    (nativePrimitiveComplex k L).homology 1 ≅ ModuleCat.of k (ULift.{u} L) :=
  HomologicalComplex.homologyMapIso (nativePrimitiveSingleIso k L) 1 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 1 (ModuleCat.of k (ULift.{u} L))

end ChevalleyEilenberg.UniverseHomologyCoalgebra

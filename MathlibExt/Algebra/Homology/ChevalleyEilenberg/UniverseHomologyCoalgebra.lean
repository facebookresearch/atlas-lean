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
# Homology coalgebras with independent carrier universes

Over a field, the Chevalley–Eilenberg coproduct and Künneth isomorphism give a natural
coaugmented graded cocommutative coalgebra on homology. The scalar field and Lie carrier may
have independent universes, and the original scalar action is retained.

The primitive chain complex has a canonical homology map to the graded primitive part of
homology, characterized by composition with the primitive-kernel inclusion.
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

/-- The canonical closed module tensor structure at the carrier height. -/
local instance originalFieldHomologyClosed : MonoidalClosed (ModuleCat.{max u v} k) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := k)

/-- The canonical CE comonoid on the unchanged chain complex. -/
local instance originalFieldChainComon : ComonObj ((canonicalChainData k L).complex : ChainComplex
  (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) := nativeComonObj k L






local instance : HasFiniteBiproducts (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) :=
  CategoryTheory.Abelian.hasFiniteBiproducts
    (C := ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)

/-- The chain tensor-unit comonoid over the field. -/
local instance chainUnitNative : ComonObj (nativeUnitComplex.{u,v} k) :=
  ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} k) ℕ)

/-- The CE comonoid in the exact original-field module category. -/
local instance chainComonoid :
    let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
      (canonicalChainData k L).complex
    ComonObj C := nativeComonObj k L
/-- The tensor-unit comonoid at the fixed original-field tensor offset. -/
local instance chainUnitComonoid : ComonObj (𝟙_ (ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k)
  ℕ)) := ComonObj.instTensorUnit _
local instance actualCoaugmentation : IsComonHom (nativeComplexCoaug k L) := nativeComplexCoaugIsComonHom k L

/-- The graded CE homology comonoid over the field, without equating the field and Lie carrier
universes. -/
def homologyComonObj : ComonObj ((HomologicalComplex.UniverseKunneth.homologyFunctor.{u,v} (R := k)).obj
    ((canonicalChainData k L).complex : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ)) := by
  let C : ChainComplex (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ :=
    (canonicalChainData k L).complex
  letI : ComonObj C := nativeComonObj k L
  exact HomologicalComplex.UniverseKunneth.comonObj.{u,v} C

/-- The coaugmentation of the original-field homology coalgebra. -/
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

/-- The pointed homology coalgebra at the offset-v unit. -/
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

/-- Lie maps preserve the independently sized homology coalgebras. -/
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

/-- The CE primitive equation uses this precise offset-v chain unit, so its identification needs
no universe shortcut. -/
theorem primitiveEquation_eq_native :
    HomologicalComplex.UniverseKunneth.primitiveEquation.{u,v} ((canonicalChainData k L).complex : ChainComplex
      (ModuleCat.UniverseScalarRestriction.Modules.{u,v} k) ℕ) (nativeComplexCoaug k L) =
      nativePrimitiveMap k L := rfl

/-- The map from homology of the unchanged primitive kernel to the primitive kernel in the field
CE homology coalgebra. -/
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

/-- On a free Lie module, primitive homology in degree one identifies with the Lie carrier lifted
into its common universe. No assertion about an isomorphism of the primitive/homology
comparison is made. -/
def primitiveHomologyOneIso [Module.Free k L] :
    (nativePrimitiveComplex k L).homology 1 ≅ ModuleCat.of k (ULift.{u} L) :=
  HomologicalComplex.homologyMapIso (nativePrimitiveSingleIso k L) 1 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.down ℕ) 1 (ModuleCat.of k (ULift.{u} L))

end ChevalleyEilenberg.UniverseHomologyCoalgebra

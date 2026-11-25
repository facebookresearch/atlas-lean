/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallExactSequenceFamilies
public import MathlibExt.AlgebraicGeometry.GeometricHallStackFunctions

/-!
# Native coherent and short-exact family stack comparisons

The fibres are the actual coherent-family and short-exact-sequence
groupoids. All reindexing comparisons use the literal map id_X × f
and the native module pullback. Their unit and composition formulas
prevent independently twisted forgetful functors. The two sequence
arrows are pulled back as their original module maps.

The three strong maps are normalized on objects, arrows and their
base-change isomorphisms. They are the subobject, quotient and middle
term of the same exact sequence, rather than freely chosen stack maps.

Reference: Bridgeland, arXiv:1002.4374v3, §3.1 and equation (15).
The native coherent-stack producer is AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b, Quot/CoherentStack.lean
and CoherentStackCategory.lean, Apache 2.0. This is its normalized
source-comparison contract; construction remains a separate request.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallFamilyStackModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open GeneralStackGeometry StackCycleGeometry StackVectorBundles
open GeometricHallStackFunctions HallExactSequenceFamilies
open StablePairParameterPullbacks

variable (X : Over (Spec (.of ℂ)))

/-- Forget to the actual module, including the original isomorphism map. -/
def familyModules (T : Over (Spec (.of ℂ))) :
    HallExactSequenceFamilies.Family X T ⥤ (StablePairFamilies.total X T).Modules where
  obj F := F.module
  map a := a.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The three terms of the original short exact sequence. -/
inductive Term
  | sub
  | middle
  | quotient
  deriving DecidableEq

/-- Each projection is the already defined native sequence functor. -/
def sequenceProjection (i : Term) (T : Over (Spec (.of ℂ))) :
    Sequence (X := X) (T := T) ⥤ HallExactSequenceFamilies.Family X T :=
  match i with
  | .sub => HallExactSequenceFamilies.subobject
  | .middle => HallExactSequenceFamilies.middleTerm
  | .quotient => HallExactSequenceFamilies.quotient

/-- The native module in a specified term of the actual sequence. -/
def sequenceModules (i : Term) (T : Over (Spec (.of ℂ))) :
    Sequence (X := X) (T := T) ⥤ (StablePairFamilies.total X T).Modules :=
  sequenceProjection X i T ⋙ familyModules X T

/-- The actual family stack and its full fibre identification. -/
structure FamilyStackData where
  carrier : LocallyFiniteTypeStack
  fibre : ∀ T : Over (Spec (.of ℂ)),
    carrier.stack.Fibre T ≌ HallExactSequenceFamilies.Family X T

namespace FamilyStackData

def moduleForget (F : FamilyStackData X) (T : Over (Spec (.of ℂ))) :=
  (F.fibre T).functor ⋙ familyModules X T

/-- Along an identity, the module base-change comparison is the native pullback unit. -/
def IsUnitCoherent (F : FamilyStackData X)
    (moduleComparison : ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull F.carrier.stack f ⋙ F.moduleForget X U ≅
        F.moduleForget X T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ (T : Over (Spec (.of ℂ))) (A : F.carrier.stack.Fibre T),
    (moduleComparison (𝟙 T)).hom.app A ≫
      (Scheme.Modules.pullbackCongr (productMap_id X T)).hom.app
        ((F.moduleForget X T).obj A) ≫
      (Scheme.Modules.pullbackId (StablePairFamilies.total X T)).hom.app
        ((F.moduleForget X T).obj A) =
    (F.moduleForget X T).map
      ((Cat.Hom.toNatIso (F.carrier.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app A)

/-- Along a composite, the module base-change comparison is the composite of the comparisons,
followed by the native pullback composition isomorphism. -/
def IsCompositionCoherent (F : FamilyStackData X)
    (moduleComparison : ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull F.carrier.stack f ⋙ F.moduleForget X U ≅
        F.moduleForget X T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ {T U V : Over (Spec (.of ℂ))} (f : U ⟶ T) (g : V ⟶ U) (A : F.carrier.stack.Fibre T),
    (moduleComparison (g ≫ f)).hom.app A ≫
      (Scheme.Modules.pullbackCongr (productMap_comp (X := X) f g)).hom.app
        ((F.moduleForget X T).obj A) =
    (F.moduleForget X V).map
      ((Cat.Hom.toNatIso
        (F.carrier.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app A) ≫
      (moduleComparison g).hom.app ((pull F.carrier.stack f).obj A) ≫
      (Scheme.Modules.pullback (productMap X g)).map ((moduleComparison f).hom.app A) ≫
      (Scheme.Modules.pullbackComp (productMap X g) (productMap X f)).hom.app
        ((F.moduleForget X T).obj A)

end FamilyStackData

/-- Every module base change is normalized to native pullback, coherently. -/
structure FamilyStackModel extends FamilyStackData X where
  moduleComparison : ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
    pull carrier.stack f ⋙ toFamilyStackData.moduleForget X U ≅
      toFamilyStackData.moduleForget X T ⋙ Scheme.Modules.pullback (productMap X f)
  unit : toFamilyStackData.IsUnitCoherent X moduleComparison
  composition : toFamilyStackData.IsCompositionCoherent X moduleComparison

namespace FamilyStackModel

def moduleForget (F : FamilyStackModel X) (T : Over (Spec (.of ℂ))) :=
  F.toFamilyStackData.moduleForget X T

end FamilyStackModel

/-- The sequence stack is compared to complete exact-sequence groupoids. -/
structure SequenceStackData where
  carrier : LocallyFiniteTypeStack
  fibre : ∀ T : Over (Spec (.of ℂ)),
    carrier.stack.Fibre T ≌ Sequence (X := X) (T := T)

namespace SequenceStackData

def moduleForget (E : SequenceStackData X) (i : Term) (T : Over (Spec (.of ℂ))) :=
  (E.fibre T).functor ⋙ sequenceModules X i T

/-- Along an identity, each term's module base-change comparison is the native pullback unit. -/
def IsUnitCoherent (E : SequenceStackData X)
    (moduleComparison : ∀ (i : Term) {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull E.carrier.stack f ⋙ E.moduleForget X i U ≅
        E.moduleForget X i T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ (i : Term) (T : Over (Spec (.of ℂ))) (A : E.carrier.stack.Fibre T),
    (moduleComparison i (𝟙 T)).hom.app A ≫
      (Scheme.Modules.pullbackCongr (productMap_id X T)).hom.app
        ((E.moduleForget X i T).obj A) ≫
      (Scheme.Modules.pullbackId (StablePairFamilies.total X T)).hom.app
        ((E.moduleForget X i T).obj A) =
    (E.moduleForget X i T).map
      ((Cat.Hom.toNatIso (E.carrier.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app A)

/-- Along a composite, each term's module base-change comparison is the composite of the
comparisons, followed by the native pullback composition isomorphism. -/
def IsCompositionCoherent (E : SequenceStackData X)
    (moduleComparison : ∀ (i : Term) {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull E.carrier.stack f ⋙ E.moduleForget X i U ≅
        E.moduleForget X i T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ (i : Term) {T U V : Over (Spec (.of ℂ))} (f : U ⟶ T) (g : V ⟶ U)
    (A : E.carrier.stack.Fibre T),
    (moduleComparison i (g ≫ f)).hom.app A ≫
      (Scheme.Modules.pullbackCongr (productMap_comp (X := X) f g)).hom.app
        ((E.moduleForget X i T).obj A) =
    (E.moduleForget X i V).map
      ((Cat.Hom.toNatIso
        (E.carrier.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app A) ≫
      (moduleComparison i g).hom.app ((pull E.carrier.stack f).obj A) ≫
      (Scheme.Modules.pullback (productMap X g)).map ((moduleComparison i f).hom.app A) ≫
      (Scheme.Modules.pullbackComp (productMap X g) (productMap X f)).hom.app
        ((E.moduleForget X i T).obj A)

/-- The comparisons carry the sequence's inclusion map to its native pullback. -/
def IsInclusionCompatible (E : SequenceStackData X)
    (moduleComparison : ∀ (i : Term) {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull E.carrier.stack f ⋙ E.moduleForget X i U ≅
        E.moduleForget X i T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T) (A : E.carrier.stack.Fibre T),
    ((E.fibre U).functor.obj ((pull E.carrier.stack f).obj A)).inclusion ≫
      (moduleComparison .middle f).hom.app A =
    (moduleComparison .sub f).hom.app A ≫
      (Scheme.Modules.pullback (productMap X f)).map ((E.fibre T).functor.obj A).inclusion

/-- The comparisons carry the sequence's projection map to its native pullback. -/
def IsProjectionCompatible (E : SequenceStackData X)
    (moduleComparison : ∀ (i : Term) {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
      pull E.carrier.stack f ⋙ E.moduleForget X i U ≅
        E.moduleForget X i T ⋙ Scheme.Modules.pullback (productMap X f)) : Prop :=
  ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T) (A : E.carrier.stack.Fibre T),
    ((E.fibre U).functor.obj ((pull E.carrier.stack f).obj A)).projection ≫
      (moduleComparison .quotient f).hom.app A =
    (moduleComparison .middle f).hom.app A ≫
      (Scheme.Modules.pullback (productMap X f)).map ((E.fibre T).functor.obj A).projection

end SequenceStackData

/-- Reindex all three terms and both actual maps by the same native pullback. -/
structure SequenceStackModel extends SequenceStackData X where
  moduleComparison : ∀ (i : Term) {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
    pull carrier.stack f ⋙ toSequenceStackData.moduleForget X i U ≅
      toSequenceStackData.moduleForget X i T ⋙ Scheme.Modules.pullback (productMap X f)
  unit : toSequenceStackData.IsUnitCoherent X moduleComparison
  composition : toSequenceStackData.IsCompositionCoherent X moduleComparison
  inclusion : toSequenceStackData.IsInclusionCompatible X moduleComparison
  projection : toSequenceStackData.IsProjectionCompatible X moduleComparison

namespace SequenceStackModel

def moduleForget (E : SequenceStackModel X) (i : Term) (T : Over (Spec (.of ℂ))) :=
  E.toSequenceStackData.moduleForget X i T

end SequenceStackModel

variable {X}

/-- A projection agrees with the actual term, naturally on every fibre. -/
structure ProjectionData (F : FamilyStackModel X) (E : SequenceStackModel X) (i : Term) where
  map : StackHom E.carrier.stack F.carrier.stack
  comparison : ∀ T : Over (Spec (.of ℂ)),
    component map T ⋙ (F.fibre T).functor ≅
      (E.fibre T).functor ⋙ sequenceProjection X i T

namespace ProjectionData

/-- The underlying module comparison is computed from the full fibre comparison. -/
def moduleIso {F : FamilyStackModel X} {E : SequenceStackModel X} {i : Term}
    (p : ProjectionData F E i) (T : Over (Spec (.of ℂ))) (A : E.carrier.stack.Fibre T) :
    (F.moduleForget X T).obj ((component p.map T).obj A) ≅
      (E.moduleForget X i T).obj A :=
  (familyModules X T).mapIso ((p.comparison T).app A)

/-- The strong naturality of the projection is tied to the module base-change comparisons of
both stacks. -/
def IsReindexCoherent {F : FamilyStackModel X} {E : SequenceStackModel X} {i : Term}
    (p : ProjectionData F E i) : Prop :=
  ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T) (A : E.carrier.stack.Fibre T),
    (F.moduleForget X U).map
      ((Cat.Hom.toNatIso (p.map.naturality f.op.toLoc)).hom.app A) ≫
      (F.moduleComparison f).hom.app ((component p.map T).obj A) ≫
      (Scheme.Modules.pullback (productMap X f)).map
        ((p.moduleIso T A).hom) =
    (p.moduleIso U ((pull E.carrier.stack f).obj A)).hom ≫
      (E.moduleComparison i f).hom.app A

end ProjectionData

/-- Strong naturality is tied to those same native module comparisons. -/
structure ProjectionModel (F : FamilyStackModel X) (E : SequenceStackModel X) (i : Term)
    extends ProjectionData F E i where
  reindex : toProjectionData.IsReindexCoherent

/-- The exact correspondence consists of the three maps of this one sequence stack. -/
structure HallStacks (X : Over (Spec (.of ℂ))) where
  families : FamilyStackModel X
  sequences : SequenceStackModel X
  subobject : ProjectionModel families sequences .sub
  quotient : ProjectionModel families sequences .quotient
  middleTerm : ProjectionModel families sequences .middle

/-- The moduli stack used in the geometric stack-function presentation. -/
abbrev HallStacks.moduli {X : Over (Spec (.of ℂ))} (H : HallStacks X) :=
  H.families.carrier.stack

end MathlibExt.AlgebraicGeometry.HallFamilyStackModels

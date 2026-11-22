/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceRawCoefficientIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputCoefficientElements

/-!
# The SAME original native raw Hom coefficient diagram

The original native endpoint Hom maps themselves define the coefficient
functor. Their actual natural comparison with the full joint-coefficient
functor proves identity and composition. The original entire input maps
give the literal augmentation into the SAME input raw coherent Hom.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceHom

open SSet.OriginalNecklace

private theorem identity_of_square {A B : SSet.{u}} (e : A ≅ B) (m : A ⟶ A)
    (h : m ≫ e.hom = e.hom ≫ 𝟙 B) : m = 𝟙 A := by
  apply (cancel_mono e.hom).1
  exact h.trans ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem composition_of_squares {A B C D E F : SSet.{u}}
    (a : A ≅ D) (b : B ≅ E) (c : C ≅ F) (m : A ⟶ B) (n : B ⟶ C) (p : A ⟶ C)
    (s : D ⟶ E) (t : E ⟶ F)
    (h₁ : m ≫ b.hom = a.hom ≫ s) (h₂ : n ≫ c.hom = b.hom ≫ t)
    (hp : p ≫ c.hom = a.hom ≫ (s ≫ t)) : p = m ≫ n := by
  apply (cancel_mono c.hom).1
  exact hp.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ t) h₁.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun f => m ≫ f) h₂.symm).trans (Category.assoc _ _ _).symm))))

/-- The SAME actual full native raw Hom identity retains the entire original identity. -/
theorem nativeHomMap_id (T : Data) : nativeHomMap.{u} (𝟙 T) = 𝟙 (hom T.object (sourceVertex T) (targetVertex T)) :=
  identity_of_square (rawCoefficientIso T) (nativeHomMap (𝟙 T))
    ((rawCoefficientIso_natural (𝟙 T)).trans
      (congrArg (fun f => (rawCoefficientIso T).hom ≫ f) (fullCoefficientFunctor.map_id T)))

/-- The SAME actual full native raw Hom maps retain both entire original maps in composition. -/
theorem nativeHomMap_comp {T U V : Data} (f : T ⟶ U) (g : U ⟶ V) :
    nativeHomMap.{u} (f ≫ g) = nativeHomMap f ≫ nativeHomMap g :=
  composition_of_squares (rawCoefficientIso T) (rawCoefficientIso U) (rawCoefficientIso V)
    (nativeHomMap f) (nativeHomMap g) (nativeHomMap (f ≫ g)) (fullCoefficientMap f) (fullCoefficientMap g)
    (rawCoefficientIso_natural f) (rawCoefficientIso_natural g)
    ((rawCoefficientIso_natural (f ≫ g)).trans
      (congrArg (fun m => (rawCoefficientIso T).hom ≫ m) (fullCoefficientFunctor.map_comp f g)))

/-- The actual full original native raw endpoint Hom functor, retaining every original map. -/
def rawCoefficientFunctor : Data ⥤ SSet.{u} where
  obj T := hom T.object (sourceVertex T) (targetVertex T)
  map f := nativeHomMap f
  map_id := nativeHomMap_id
  map_comp := nativeHomMap_comp

/-- Both original full native coefficient functors have their SAME actual natural inverse comparison. -/
def rawCoefficientNatIso : rawCoefficientFunctor.{u} ≅ fullCoefficientFunctor.{u} :=
  NatIso.ofComponents rawCoefficientIso (fun f => rawCoefficientIso_natural f)

end CategoryTheory.CoherentRealization.OriginalNecklaceHom

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open OriginalNecklaceHom

/-- The genuine original raw Hom coefficient diagram over the SAME entire native input category. -/
def rawCoefficientDiagram (K : SSet.{u}) (x y : K _⦋0⦌) : Object K x y ⥤ SSet.{u} :=
  forget K x y ⋙ rawCoefficientFunctor

/-- Both actual full original coefficient diagrams retain their SAME objectwise natural isomorphism. -/
def rawCoefficientDiagramIso (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawCoefficientDiagram K x y ≅ fullCoefficientDiagram K x y :=
  NatIso.ofComponents (fun T => rawCoefficientIso T.necklace)
    (fun f => rawCoefficientIso_natural f.necklaceMap)

variable {K : SSet.{u}} {x y : K _⦋0⦌}

/-- The SAME entire original input map retains its original source vertex. -/
theorem input_source (T : Object K x y) : T.input.app (op ⦋0⦌) (sourceVertex T.necklace) = x :=
  (SSet.yonedaEquiv_comp T.necklace.source T.input).symm.trans T.source_eq

/-- The SAME entire original input map retains its original target vertex. -/
theorem input_target (T : Object K x y) : T.input.app (op ⦋0⦌) (targetVertex T.necklace) = y :=
  (SSet.yonedaEquiv_comp T.necklace.target T.input).symm.trans T.target_eq

/-- The complete original native input Hom map into the SAME original raw input Hom. -/
def inputHomMap (T : Object K x y) :
    hom T.necklace.object.{u} (sourceVertex T.necklace) (targetVertex T.necklace) ⟶ hom K x y :=
  pointedHomMap T.input (input_source T) (input_target T)

/-- Every original native input-map morphism retains the SAME full input Hom square. -/
theorem inputHomMap_natural {T U : Object K x y} (f : T ⟶ U) :
    nativeHomMap f.necklaceMap ≫ inputHomMap U = inputHomMap T :=
  (pointedHomMap_comp f.necklaceMap.map U.input (nativeMap_source f.necklaceMap)
    (nativeMap_target f.necklaceMap) (input_source U) (input_target U)).trans
      (pointedHomMap_eq f.over
        ((congrArg (fun v => U.input.app (op ⦋0⦌) v) (nativeMap_source f.necklaceMap)).trans (input_source U))
        ((congrArg (fun v => U.input.app (op ⦋0⦌) v) (nativeMap_target f.necklaceMap)).trans (input_target U))
        (input_source T) (input_target T))

/-- The full original raw native Hom coefficient augmentation retains every original input map. -/
def rawInputAugmentation (K : SSet.{u}) (x y : K _⦋0⦌) :
    rawCoefficientDiagram K x y ⟶ (Functor.const (Object K x y)).obj (hom K x y) where
  app T := inputHomMap T
  naturality T U f := by
    change nativeHomMap f.necklaceMap ≫ inputHomMap U = inputHomMap T ≫ 𝟙 (hom K x y)
    exact (inputHomMap_natural f).trans (Category.comp_id _).symm

/-- Every original raw diagram coefficient map is the SAME full native input Hom map. -/
theorem rawInputAugmentation_app (T : Object K x y) : (rawInputAugmentation K x y).app T = inputHomMap T := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceInput

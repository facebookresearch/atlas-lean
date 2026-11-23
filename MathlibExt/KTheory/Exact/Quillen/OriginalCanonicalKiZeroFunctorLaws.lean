/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.OriginalCanonicalKiFunctorLaws

/-!
# Current Ki functor laws on every original path component

Degree zero uses the existing component map of the actual K-space functor.
The original whole composition and natural-isomorphism homotopies give its
functor laws on every component. Together with the original positive laws,
these retain the actual all-degree map on every original carrier.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Topology

universe uC vC uD vD uE vE

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- The current degree-zero map preserves composition on every original component. -/
theorem NQKSpaceFunctorKiMap_zero_original_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]
    (a : HomotopyGroup.Pi 0 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap (F ⋙ G) 0 a =
      NQKSpaceFunctorKiMap G 0 (NQKSpaceFunctorKiMap F 0 a) := by
  let pC := HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C))
  let pE := HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace E) (x := Path.refl (NQReal.basepoint E))
  let componentF : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace D) :=
    ZerothHomotopy.lift
      (fun x : NQKSpace C => ZerothHomotopy.mk ((NQKSpaceFunctorMap F) x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous))
  let componentG : ZerothHomotopy (NQKSpace D) → ZerothHomotopy (NQKSpace E) :=
    ZerothHomotopy.lift
      (fun x : NQKSpace D => ZerothHomotopy.mk ((NQKSpaceFunctorMap G) x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap G).continuous))
  let componentFG : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace E) :=
    ZerothHomotopy.lift
      (fun x : NQKSpace C => ZerothHomotopy.mk ((NQKSpaceFunctorMap (F ⋙ G)) x))
      (fun {_ _} p =>
        ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap (F ⋙ G)).continuous))
  have hComponents (c : ZerothHomotopy (NQKSpace C)) :
      componentFG c = componentG (componentF c) := by
    induction c using ZerothHomotopy.rec with
    | mk gamma =>
      exact ZerothHomotopy.sound
        ((NQKSpaceFunctorOriginalCompHomotopy F G).evalAt gamma)
  have hF := NQKSpaceFunctorKiMap_zero_components F a
  have hG := NQKSpaceFunctorKiMap_zero_components G (NQKSpaceFunctorKiMap F 0 a)
  have hFG := NQKSpaceFunctorKiMap_zero_components (F ⋙ G) a
  apply pE.injective
  exact hFG.trans ((hComponents (pC a)).trans
    ((congrArg componentG hF).symm.trans hG.symm))

/-- An actual natural isomorphism gives equality on every degree-zero component. -/
theorem NQKSpaceFunctorKiMap_zero_original_natIso (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (a : HomotopyGroup.Pi 0 (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F 0 a = NQKSpaceFunctorKiMap G 0 a := by
  let pC := HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace C) (x := Path.refl (NQReal.basepoint C))
  let pD := HomotopyGroup.pi0EquivZerothHomotopy
    (X := NQKSpace D) (x := Path.refl (NQReal.basepoint D))
  let componentF : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace D) :=
    ZerothHomotopy.lift
      (fun x : NQKSpace C => ZerothHomotopy.mk ((NQKSpaceFunctorMap F) x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap F).continuous))
  let componentG : ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace D) :=
    ZerothHomotopy.lift
      (fun x : NQKSpace C => ZerothHomotopy.mk ((NQKSpaceFunctorMap G) x))
      (fun {_ _} p => ZerothHomotopy.sound (p.map (NQKSpaceFunctorMap G).continuous))
  have hComponents (c : ZerothHomotopy (NQKSpace C)) :
      componentF c = componentG c := by
    induction c using ZerothHomotopy.rec with
    | mk gamma =>
      exact ZerothHomotopy.sound ((NQKSpaceFunctorNatIsoHomotopy F G e).evalAt gamma)
  apply pD.injective
  exact (NQKSpaceFunctorKiMap_zero_components F a).trans
    ((hComponents (pC a)).trans (NQKSpaceFunctorKiMap_zero_components G a).symm)

/-- Every index of the original current Ki map preserves actual functor composition. -/
theorem NQKSpaceFunctorKiMap_allIndices_original_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (n : ℕ)
    (a : HomotopyGroup.Pi n (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap (F ⋙ G) n a =
      NQKSpaceFunctorKiMap G n (NQKSpaceFunctorKiMap F n a) := by
  cases n with
  | zero => exact NQKSpaceFunctorKiMap_zero_original_comp F G a
  | succ n => exact NQKSpaceFunctorKiMap_original_comp F G n a

/-- The actual natural-isomorphism family transports every index of current Ki. -/
theorem NQKSpaceFunctorKiMap_allIndices_original_natIso (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) (n : ℕ)
    (a : HomotopyGroup.Pi n (NQKSpace C) (Path.refl (NQReal.basepoint C))) :
    NQKSpaceFunctorKiMap F n a = NQKSpaceFunctorKiMap G n a := by
  cases n with
  | zero => exact NQKSpaceFunctorKiMap_zero_original_natIso F G e a
  | succ n => exact NQKSpaceFunctorKiMap_original_natIso F G e n a

end AlgebraicKTheory

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceBasedPositive
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

/-!
# Connecting equivalences at arbitrary simplicial loop vertices

The canonical rerooted based-path fibration gives an equivalence in every
literal homotopy degree. Both complete functions, the actual fiber comparison,
and naturality at arbitrary source and target loop vertices are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace SSet

/-- The actual canonical rerooted fiber keeps its given vertex through the full pi Iso. -/
def fiberAtVertexPiEquiv (X : SSet.{v}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    SSet.KanComplex.π k (SSet.loopFibrationSequenceAtVertex X x z).fiber
        (SSet.loopFibrationSequenceAtVertex X x z).fiberPoint ≃
      SSet.KanComplex.π k (SSet.loopSpace X x) z :=
  SSet.KanComplex.π.equivOfIso (Iso.refl (SSet.loopSpace X x))
    (SSet.loopFibrationSequenceAtVertex_fiberPoint X x z) k

/-- Both entire connecting functions use the existing canonical rerooted sequence. -/
def connectingAtVertexEquiv (X : SSet.{v}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    SSet.KanComplex.π (k + 1) X x ≃ SSet.KanComplex.π k (SSet.loopSpace X x) z :=
  (Equiv.ofBijective ((SSet.loopFibrationSequenceAtVertex X x z).connectingMap k)
    (SSet.loopFibrationSequenceAtVertex_connectingMap_bijective X x z k)).trans
      (fiberAtVertexPiEquiv X x z k)

/-- The whole forward function is the actual canonical connecting map and genuine fiber map. -/
theorem connectingAtVertexEquiv_whole (X : SSet.{v}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    (fun q => connectingAtVertexEquiv X x z k q) =
      (fun q => fiberAtVertexPiEquiv X x z k
        ((SSet.loopFibrationSequenceAtVertex X x z).connectingMap k q)) := rfl

/-- Both complete inverse functions retain the same actual canonical connecting and fiber maps. -/
theorem connectingAtVertexEquiv_inverse_whole (X : SSet.{v}) [SSet.KanComplex X]
    (x : X _⦋0⦌) (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    (fun q => (connectingAtVertexEquiv X x z k).symm q) =
      (fun q => (Equiv.ofBijective
        ((SSet.loopFibrationSequenceAtVertex X x z).connectingMap k)
        (SSet.loopFibrationSequenceAtVertex_connectingMap_bijective X x z k)).symm
          ((fiberAtVertexPiEquiv X x z k).symm q)) := rfl

/-- The whole canonical rerooted morphism gives the complete forward connecting square. -/
theorem connectingAtVertexEquiv_naturality {X Y : SSet.{v}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    SSet.KanComplex.π.map (SSet.loopSpaceMap f h) rfl k ∘ connectingAtVertexEquiv X x z k =
      connectingAtVertexEquiv Y y ((SSet.loopSpaceMap f h).app _ z) k ∘
        SSet.KanComplex.π.map f h (k + 1) := by
  funext q
  let F := SSet.loopFibrationSequenceAtVertexHom f h z
  let e := Iso.refl (SSet.loopSpace X x)
  let t := Iso.refl (SSet.loopSpace Y y)
  have hs : F.fiberMap ≫ t.hom = e.hom ≫ SSet.loopSpaceMap f h :=
    (Category.comp_id _).trans
      ((SSet.loopFibrationSequenceAtVertexHom_fiberMap f h z).trans (Category.id_comp _).symm)
  have hp := SSet.KanComplex.π.map_square e.hom t.hom
    F.fiberMap (SSet.loopSpaceMap f h) hs
    (SSet.loopFibrationSequenceAtVertex_fiberPoint X x z)
    (SSet.loopFibrationSequenceAtVertex_fiberPoint Y y ((SSet.loopSpaceMap f h).app _ z))
    F.fiberMap_app_basePoint rfl k
    ((SSet.loopFibrationSequenceAtVertex X x z).connectingMap k q)
  have hd := SSet.loopFibrationSequenceAtVertex_connectingMap_naturality f h z k q
  exact hp.symm.trans
    (congrArg (fiberAtVertexPiEquiv Y y ((SSet.loopSpaceMap f h).app _ z) k) hd)

/-- Every complete inverse square uses the actual inverse of the same canonical source functions. -/
theorem connectingAtVertexEquiv_inverse_naturality {X Y : SSet.{v}}
    [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y)
    (z : SSet.loopSpace X x _⦋0⦌) (k : ℕ) :
    SSet.KanComplex.π.map f h (k + 1) ∘ (connectingAtVertexEquiv X x z k).symm =
      (connectingAtVertexEquiv Y y ((SSet.loopSpaceMap f h).app _ z) k).symm ∘
        SSet.KanComplex.π.map (SSet.loopSpaceMap f h) rfl k := by
  funext q
  let e := connectingAtVertexEquiv X x z k
  let t := connectingAtVertexEquiv Y y ((SSet.loopSpaceMap f h).app _ z) k
  let l := SSet.KanComplex.π.map (SSet.loopSpaceMap f h) rfl k (x := z)
  apply t.injective
  have hn := congrFun (connectingAtVertexEquiv_naturality f h z k) (e.symm q)
  exact hn.symm.trans ((congrArg l (e.apply_symm_apply q)).trans
    (t.apply_symm_apply (l q)).symm)

/-- The whole original inverse connecting square retains the GIVEN actual target vertex. -/
theorem connectingAtVertexEquiv_inverse_naturality_at_target {X Y : SSet.{v}} [SSet.KanComplex X]
    [SSet.KanComplex Y] (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (h : f.app _ x = y) (z : SSet.loopSpace X x _⦋0⦌) (w : SSet.loopSpace Y y _⦋0⦌)
    (hw : (SSet.loopSpaceMap f h).app _ z = w) (k : ℕ) :
    SSet.KanComplex.π.map f h (k + 1) ∘
        (connectingAtVertexEquiv X x z k).symm =
      (connectingAtVertexEquiv Y y w k).symm ∘
        SSet.KanComplex.π.map (SSet.loopSpaceMap f h) hw k := by
  cases hw
  exact connectingAtVertexEquiv_inverse_naturality f h z k

end SSet

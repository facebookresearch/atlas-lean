/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Languages.LambdaCalculus.SystemF.FreeTheorems

/-! # Free-theorem consumers, encodings and non-vacuity checks -/

namespace Cslib.Languages.LambdaCalculus.SystemF

/-! ### Encodings -/

-- An erased two-element list folds its arguments in order.
example (x y n c : Model) :
    BetaEq (Model.app (Model.app (encList [x, y]) n) c)
      (Model.app (Model.app c x) (Model.app (Model.app c y) n)) := by
  exact ((Tm.close_beta (fun i => [x, y].get i) (.var 0)
    (.lam (.arr (.var 1) (.arr (.var 0) (.var 0))) (encListBody 2 (List.finRange 2))) n).appFun
      c).trans (Tm.close_beta _ _ _ c)

-- The erased encoded map applies the function to every element, under the fold.
example (A B : Ty 0) (f x y n c : Model) :
    BetaEq (Model.app (Model.app (mapE A B f (encList [x, y])) n) c)
      (Model.app (Model.app c (Model.app f x))
        (Model.app (Model.app c (Model.app f y)) n)) := by
  refine ((((Tm.close_beta Fin.elim0 (.arr (.var 1) (.var 0)) _ f).appFun _).appFun n).appFun
    c).trans ?_
  refine (((Tm.close_beta _ (listTy (.var 1)) _ _).appFun n).appFun c).trans ?_
  refine ((Tm.close_beta _ (.var 0) _ n).appFun c).trans ?_
  refine (Tm.close_beta _ (.arr (.var 1) (.arr (.var 0) (.var 0))) _ c).trans ?_
  change BetaEq (Model.app (Model.app (encList [x, y]) n)
    (Tm.close (Fin.cases c (Fin.cases n (Fin.cases (encList [x, y]) (Fin.cases f Fin.elim0))))
      (.lam (.var 2) (.lam (.var 0) (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0))) :
        Tm 3 4))) _
  refine (((Tm.close_beta (fun i => [x, y].get i) (.var 0)
    (.lam (.arr (.var 1) (.arr (.var 0) (.var 0))) (encListBody 2 (List.finRange 2))) n).appFun
      _).trans (Tm.close_beta _ _ _ _)).trans ?_
  change BetaEq (Model.app (Model.app
    (Tm.close (Fin.cases c (Fin.cases n (Fin.cases (encList [x, y]) (Fin.cases f Fin.elim0))))
        (.lam (.var 2) (.lam (.var 0) (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0))) :
          Tm 3 4)) x)
    (Model.app (Model.app
    (Tm.close (Fin.cases c (Fin.cases n (Fin.cases (encList [x, y]) (Fin.cases f Fin.elim0))))
        (.lam (.var 2) (.lam (.var 0) (.app (.app (.var 2) (.app (.var 5) (.var 1))) (.var 0))) :
          Tm 3 4)) y) n)) _
  refine BetaEq.trans
    (BetaEq.appArg _ (((Tm.close_beta _ _ _ y).appFun n).trans (Tm.close_beta _ _ _ n))) ?_
  exact ((Tm.close_beta _ _ _ x).appFun _).trans (Tm.close_beta _ _ _ _)

-- Every encoding is typed.
example : Typing Fin.elim0 mapTm mapTy := mapTm_typed
example : Typing Fin.elim0 unaryPackage packageTy := unaryPackage_typed
example : Typing Fin.elim0 accumulatorPackage packageTy := accumulatorPackage_typed
example : Typing Fin.elim0 stuckPackage packageTy := stuckPackage_typed
example : Typing Fin.elim0 distinguishingClient (.arr packageTy natTy) :=
  distinguishingClient_typed

-- The graph relation relates an argument to its image.
example (f a : Model) : (Rel.graph f).holds a (Model.app f a) := BetaEq.refl _

/-! ### Identity -/

example (x : Model) :
    BetaEq (Model.app (Tm.eraseModel (.tapp (polyId : Tm 0 0) (.arr natTy natTy))) x) x :=
  polymorphic_identity (polyId_typed Fin.elim0) (.arr natTy natTy) x

/-! ### Naturality at a list-doubling rearrangement -/

/-- **List doubling.** The rearrangement `l ↦ l ++ l`, as the term
`ΛX. λl. ΛR. λn. λc. l [R] (l [R] n c) c`. -/
private def doubleTm : Tm 0 0 :=
  .tabs (.lam (listTy (.var 0)) (.tabs (.lam (.var 0)
    (.lam (.arr (.var 1) (.arr (.var 0) (.var 0)))
      (.app (.app (.tapp (.var 2) (.var 0))
        (.app (.app (.tapp (.var 2) (.var 0)) (.var 1)) (.var 0))) (.var 0))))))

private theorem doubleTm_typed : Typing Fin.elim0 doubleTm rearrangeTy := by
  exact .tabs (.lam (.tabs (.lam (.lam (.app (.app
    (.tapp (C := .arr (.var 0) (.arr (.arr (.var 2) (.arr (.var 0) (.var 0))) (.var 0))) (.var 2))
    (.app (.app
      (.tapp (C := .arr (.var 0) (.arr (.arr (.var 2) (.arr (.var 0) (.var 0))) (.var 0)))
        (.var 2)) (.var 1)) (.var 0))) (.var 0))))))

-- Naturality on a two-element list, with element types that differ.
example (f x y n c : Model) :
    BetaEq
      (Model.app (Model.app
        (mapE natTy accTy f (Model.app (Tm.eraseModel (.tapp doubleTm natTy)) (encList [x, y])))
        n) c)
      (Model.app (Model.app
        (Model.app (Tm.eraseModel (.tapp doubleTm accTy)) (mapE natTy accTy f (encList [x, y])))
        n) c) :=
  rearrangement_natural doubleTm_typed natTy accTy f [x, y] n c

-- List doubling folds the list twice, so it is not the identity rearrangement.
example (x y n c : Model) :
    BetaEq
      (Model.app (Model.app
        (Model.app (Tm.eraseModel (.tapp doubleTm natTy)) (encList [x, y])) n) c)
      (Model.app (Model.app c x) (Model.app (Model.app c y)
        (Model.app (Model.app c x) (Model.app (Model.app c y) n)))) := by
  have hfold : ∀ N : Model, BetaEq (Model.app (Model.app (encList [x, y]) N) c)
      (Model.app (Model.app c x) (Model.app (Model.app c y) N)) := fun N =>
    ((Tm.close_beta (fun i => [x, y].get i) (.var 0)
      (.lam (.arr (.var 1) (.arr (.var 0) (.var 0))) (encListBody 2 (List.finRange 2)))
        N).appFun c).trans (Tm.close_beta _ _ _ c)
  refine (((Tm.close_beta (n := 1) Fin.elim0 (listTy (.var 0)) _ _).appFun n).appFun
    c).trans ?_
  refine ((Tm.close_beta (n := 2) _ (.var 0) _ n).appFun c).trans ?_
  refine (Tm.close_beta (n := 2) _ (.arr (.var 1) (.arr (.var 0) (.var 0))) _ c).trans ?_
  change BetaEq (Model.app (Model.app (encList [x, y])
    (Model.app (Model.app (encList [x, y]) n) c)) c) _
  exact (hfold _).trans (BetaEq.appArg _ (BetaEq.appArg _ (hfold n)))

-- The element-replacing function fails naturality.
example : ¬ BetaEq
    (Model.app (Model.app
      (mapE natTy natTy (Model.atom 1) (Model.app constRearrange (encList [Model.atom 2])))
      (Model.atom 3)) (Model.atom 4))
    (Model.app (Model.app
      (Model.app constRearrange (mapE natTy natTy (Model.atom 1) (encList [Model.atom 2])))
      (Model.atom 3)) (Model.atom 4)) :=
  constRearrange_not_natural natTy natTy

/-! ### Representation independence -/

-- The counter relation relates the states after two increments.
example : counterRel.holds
    (Model.app (Tm.eraseModel (succTm : Tm 0 0))
      (Model.app (Tm.eraseModel (succTm : Tm 0 0)) (Tm.eraseModel (zeroTm : Tm 0 0))))
    (Model.app (Tm.eraseModel accInc) (Model.app (Tm.eraseModel accInc) (Tm.eraseModel accNew))) :=
  counterRel_inc (counterRel_inc counterRel_new)

-- The counter relation is not total: zero is not related to the incremented accumulator.
example : ¬ counterRel.holds (Tm.eraseModel (zeroTm : Tm 0 0))
    (Model.app (Tm.eraseModel accInc) (Tm.eraseModel accNew)) := by
  rintro ⟨k, h1, h2⟩
  have hz : ∀ s w : Model,
      BetaEq (Model.app (Model.app (Tm.eraseModel (zeroTm : Tm 0 0)) s) w) w := fun s w =>
    ((Tm.close_beta (n := 1) Fin.elim0 (.arr (.var 0) (.var 0)) (.lam (.var 0) (.var 0))
      s).appFun w).trans (Tm.close_beta _ _ _ w)
  have hH : ∀ m s w : Model, BetaEq (Model.app (Model.app (Model.app
      (Model.app (Tm.eraseModel accInc) (Tm.eraseModel accNew)) m) s) w)
      (Model.app s (Model.app (Model.app m s) w)) := by
    intro m s w
    refine ((((Tm.close_beta Fin.elim0 accTy _ _).appFun m).appFun s).appFun w).trans ?_
    refine (((Tm.close_beta _ natTy _ m).appFun s).appFun w).trans ?_
    simp only [Tm.close_app, Tm.close_var]
    refine BetaEq.trans (g := Model.app s
      (Model.app (Model.app (Model.app (Tm.eraseModel accNew) m) s) w)) ?_ ?_
    · exact (((Tm.close_beta _ natTy _ _).appFun s).appFun w).trans
        (((Tm.close_beta (n := 1) _ (.arr (.var 0) (.var 0)) _ s).appFun w).trans
          (Tm.close_beta _ _ _ w))
    · exact BetaEq.appArg s (((Tm.close_beta Fin.elim0 natTy _ m).appFun s).appFun w)
  have hsw : ∀ s w : Model, BetaEq (Model.app s w) w := fun s w =>
    (BetaEq.appArg s (hz s w).symm).trans ((hH _ s w).symm.trans ((h2 _ s w).trans
      ((h1 s _).symm.trans ((hz s _).trans (hz s w)))))
  have hall : ∀ b w : Model, BetaEq b w := fun b w =>
    (Tm.close_beta (fun _ : Fin 1 => b) natTy (.var 1 : Tm 0 2) w).symm.trans (hsw _ w)
  exact not_exists_simulation_unary_stuck ⟨Rel.total, trivial, fun _ _ _ => trivial,
    fun x y _ S s s' _ z z' hzz => (S.congr (hall _ z) (hall _ z')).mpr hzz⟩

-- The unary and accumulator counters agree on the distinguishing client.
example : BetaEq
    (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
      (Tm.eraseModel unaryPackage)) (Model.atom 0)) (Model.atom 1))
    (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
      (Tm.eraseModel accumulatorPackage)) (Model.atom 0)) (Model.atom 1)) :=
  counters_indistinguishable distinguishingClient_typed (Model.atom 0) (Model.atom 1)

/-! ### Non-vacuity -/

example : ¬ BetaEq
    (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
      (Tm.eraseModel unaryPackage)) (Model.atom 0)) (Model.atom 1))
    (Model.app (Model.app (Model.app (Tm.eraseModel distinguishingClient)
      (Tm.eraseModel stuckPackage)) (Model.atom 0)) (Model.atom 1)) :=
  stuck_counter_distinguished

example : ¬ ∃ R : Rel, R.holds (Tm.eraseModel (zeroTm : Tm 0 0)) (Tm.eraseModel (zeroTm : Tm 0 0)) ∧
    (∀ x y, R.holds x y →
      R.holds (Model.app (Tm.eraseModel (succTm : Tm 0 0)) x)
        (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) y)) ∧
    ∀ x y, R.holds x y →
      ((natTy : Ty 0).interpret Fin.elim0).holds
        (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) x)
        (Model.app (Tm.eraseModel (idTm natTy : Tm 0 0)) y) :=
  not_exists_simulation_unary_stuck

end Cslib.Languages.LambdaCalculus.SystemF

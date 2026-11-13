/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectVerticalWindingCutCollision
import Code.FrontierD.IntegerUnitStepPlateau











open SimpleGraph

namespace StatMech.FrontierD

noncomputable section



theorem fkRectMedialBoundaryPrimalSeamTrace_add
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (m n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + n) =
      fkRectMedialBoundaryPrimalSeamTrace R pairing d m +
        fkRectMedialBoundaryPrimalSeamTrace R pairing
          ((fkMedialBoundaryStep pairing)^[m] d) n := by
  induction m generalizing d with
  | zero =>
      simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ m ih =>
      simp only [Nat.succ_add, fkRectMedialBoundaryPrimalSeamTrace]
      rw [ih]
      rw [Function.iterate_succ_apply]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring



theorem fkRectMedialBoundaryPrimalSeamTrace_succ
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (m : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + 1) =
      fkRectMedialBoundaryPrimalSeamTrace R pairing d m +
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[m] d) := by
  rw [fkRectMedialBoundaryPrimalSeamTrace_add]
  simp [fkRectMedialBoundaryPrimalSeamTrace]


theorem fkRectVerticalSeamIncrement_bounds
    (R : FKRectTorus) (x y : R.Vertex) :
    -1 ≤ fkRectVerticalSeamIncrement R x y ∧
      fkRectVerticalSeamIncrement R x y ≤ 1 := by
  unfold fkRectVerticalSeamIncrement
  split
  · norm_num
  · split <;> norm_num


theorem fkRectBlackBoundaryPrefixVerticalLevel_unitSteps
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    IntUnitSteps (fun m =>
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  change IntUnitSteps (fun m =>
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2)
  intro m
  have hsucc := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 m
  have hbound := fkRectVerticalSeamIncrement_bounds R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[m] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[m] d.1)))
  change -1 ≤
      (fkRectMedialBoundaryPrimalSeamIncrement R pairing
        ((fkMedialBoundaryStep pairing)^[m] d.1)).2 ∧
    (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[m] d.1)).2 ≤ 1 at hbound
  have hsnd := congrArg Prod.snd hsucc
  simp only [Prod.snd_add] at hsnd
  change
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (m + 1)).2 ≤
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 + 1 ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 ≤
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (m + 1)).2 + 1
  constructor <;> omega



theorem fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (2 * n)).2 =
      2 * (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have hadd := fkRectMedialBoundaryPrimalSeamTrace_add
    R pairing d.1 n n
  rw [hdart] at hadd
  have hwind := fkRectBlackBoundaryPrimalCycleWalk_winding R omega d
  change fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
    fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n at hwind
  have hsnd := congrArg Prod.snd hadd
  simp only [Prod.snd_add] at hsnd
  rw [show 2 * n = n + n by omega, hsnd, ← hwind]
  ring



theorem exists_fkRectBlackBoundaryUnitPlateauEndpoints
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    let r : Int := j.val + 1
    ∃ ab : Nat × Nat,
      0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
          (ab.1 - 1)).2 = r - 1 ∧
        (∀ m, ab.1 ≤ m → m ≤ ab.2 →
          (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
        (∀ m < ab.2 + 1,
          (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
          (ab.2 + 1)).2 = r + 1 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let f : Nat → Int := fun m =>
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2
  have hunit : IntUnitSteps f := by
    exact fkRectBlackBoundaryPrefixVerticalLevel_unitSteps R omega d
  have hzero : f 0 = 0 := rfl
  let r : Int := j.val + 1
  have hr : 0 < r := by simp [r]
  have hk : ((fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat : Int) =
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    rw [Int.toNat_of_nonneg hpos.le]
  have hj : (j.val : Int) + 1 ≤
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    calc
      (j.val : Int) + 1 ≤
          ((fkRectWalkWinding R
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat : Int) := by
        exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
      _ = _ := hk
  have hreach : r + 1 ≤ f (2 * n) := by
    dsimp [f, n, pairing]
    rw [fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd]
    dsimp [r]
    omega
  rcases exists_intUnitStep_bracketedPlateau hunit hzero hr hreach with
    ⟨a, b, hs⟩
  exact ⟨(a, b), hs⟩



noncomputable def fkRectBlackBoundaryUnitPlateauEndpoints
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    Nat × Nat :=
  Classical.choose
    (exists_fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j)


theorem fkRectBlackBoundaryUnitPlateauEndpoints_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    let ab := fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j
    let r : Int := j.val + 1
    0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (ab.1 - 1)).2 = r - 1 ∧
      (∀ m, ab.1 ≤ m → m ≤ ab.2 →
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
      (∀ m < ab.2 + 1,
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (ab.2 + 1)).2 = r + 1 := by
  exact Classical.choose_spec
    (exists_fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j)



theorem fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (e : FKMedialDart R.medialTorus)
    (hzero : (fkRectMedialBoundaryPrimalSeamIncrement R
      (fkRectConfigurationToMedialPairing R omega) e).2 = 0) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Reachable
        (fkRectMedialDartPrimalLabel R e)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) e)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  rcases fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj
      R omega e with heq | hadj
  · rw [heq]
  · apply (fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam
      R omega hadj ?_).reachable
    intro hcross
    exact (fkRectVerticalSeamIncrement_ne_zero_of_crosses
      R _ _ hcross) hzero



theorem fkRectBlackBoundaryPlateau_cutReachable
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) {a b : Nat}
    (hab : a ≤ b)
    (hconst : ∀ m, a ≤ m → m ≤ b →
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d.1 m).2 =
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d.1 a).2) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Reachable
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega))^[a] d.1))
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega))^[b] d.1)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => exact Reachable.refl _
  | succ k ih =>
      have hprefix := fkRectMedialBoundaryPrimalSeamTrace_succ
        R pairing d.1 (a + k)
      have hlevel0 := hconst (a + k) (by omega) (by omega)
      have hlevel1 := hconst (a + k + 1) (by omega) (by omega)
      change (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (a + k)).2 = _ at hlevel0
      change (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (a + k + 1)).2 = _ at hlevel1
      have hinc : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[a + k] d.1)).2 = 0 := by
        have hsnd := congrArg Prod.snd hprefix
        simp only [Prod.snd_add] at hsnd
        omega
      have hreach :=
        fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero
          R omega ((fkMedialBoundaryStep pairing)^[a + k] d.1) hinc
      have hreach' :
          (fkRectOpenGraph R
            (fkRectForceHorizontalCutClosed R omega)).Reachable
              (fkRectMedialDartPrimalLabel R
                ((fkMedialBoundaryStep pairing)^[a + k] d.1))
              (fkRectMedialDartPrimalLabel R
                ((fkMedialBoundaryStep pairing)^[a + (k + 1)] d.1)) := by
        rw [show a + (k + 1) = (a + k) + 1 by omega,
          Function.iterate_succ_apply']
        exact hreach
      exact (ih (by omega)
        (fun m ham hmk => hconst m ham (by omega))).trans hreach'



theorem fkRectVerticalSeamIncrement_eq_one_endpoints
    (R : FKRectTorus) (x y : R.Vertex)
    (hinc : fkRectVerticalSeamIncrement R x y = 1) :
    x.2 = fkRectTopRow R ∧ y.2 = fkRectBottomRow R := by
  unfold fkRectVerticalSeamIncrement at hinc
  split at hinc
  · rename_i h
    constructor
    · apply Fin.ext
      simp [fkRectTopRow]
      omega
    · apply Fin.ext
      simp [fkRectBottomRow]
      omega
  · split at hinc <;> norm_num at hinc



noncomputable def fkRectBlackBoundaryUnitCutComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent :=
  let pairing := fkRectConfigurationToMedialPairing R omega
  let a := (fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j).1
  (fkRectOpenGraph R
    (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
      (fkRectMedialDartPrimalLabel R
        ((fkMedialBoundaryStep pairing)^[a] d.1))



theorem fkRectBlackBoundaryUnitCutComponent_crossing
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega)
      (fkRectBlackBoundaryUnitCutComponent R omega d hpos j) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let ab := fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j
  let a := ab.1
  let b := ab.2
  let r : Int := j.val + 1
  have hs := fkRectBlackBoundaryUnitPlateauEndpoints_spec
    R omega d hpos j
  change 0 < a ∧ a ≤ b ∧ b < _ ∧
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (a - 1)).2 = r - 1 ∧
    (∀ m, a ≤ m → m ≤ b →
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
    (∀ m < b + 1,
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (b + 1)).2 = r + 1 at hs
  rcases hs with ⟨hapos, hab, hbN, hprev, hconst, hfirst, hnext⟩
  have hentryPrefix := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 (a - 1)
  have haLevel := hconst a le_rfl hab
  have hentry : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1)).2 = 1 := by
    have hsnd := congrArg Prod.snd hentryPrefix
    simp only [Prod.snd_add] at hsnd
    have hidx : a - 1 + 1 = a := by omega
    rw [hidx] at hsnd
    omega
  have hentryRows := fkRectVerticalSeamIncrement_eq_one_endpoints R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[a - 1] d.1))) hentry
  have haIter : (fkMedialBoundaryStep pairing
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1)) =
      (fkMedialBoundaryStep pairing)^[a] d.1 := by
    rw [show a = (a - 1) + 1 by omega]
    exact (Function.iterate_succ_apply'
      (fkMedialBoundaryStep pairing) (a - 1) d.1).symm
  rw [haIter] at hentryRows
  have hexitPrefix := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 b
  have hbLevel := hconst b hab le_rfl
  have hexit : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[b] d.1)).2 = 1 := by
    have hsnd := congrArg Prod.snd hexitPrefix
    simp only [Prod.snd_add] at hsnd
    omega
  have hexitRows := fkRectVerticalSeamIncrement_eq_one_endpoints R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[b] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[b] d.1))) hexit
  have hreach := fkRectBlackBoundaryPlateau_cutReachable
    R omega d hab (by
      intro m ham hmb
      rw [hconst m ham hmb, haLevel])
  refine ⟨⟨(fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[a] d.1)).1, ?_⟩,
    ⟨(fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[b] d.1)).1, ?_⟩⟩
  · unfold fkRectBlackBoundaryUnitCutComponent
    dsimp only
    apply congrArg (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
    exact Prod.ext rfl hentryRows.2.symm
  · unfold fkRectBlackBoundaryUnitCutComponent
    dsimp only
    have hbvertex :
        ((fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep pairing)^[b] d.1)).1,
            fkRectTopRow R) =
          fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep pairing)^[b] d.1) :=
      Prod.ext rfl hexitRows.1.symm
    rw [hbvertex]
    exact (ConnectedComponent.sound hreach).symm

end

end StatMech.FrontierD

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicKilledKernel











namespace StatMech.Universality


def isingDiagonalWalkDisplacement (steps : List (Int × Int)) : Int × Int :=
  ((steps.map Prod.fst).sum, (steps.map Prod.snd).sum)


def isingDiagonalWalkEndpoint (start : Int × Int)
    (steps : List (Int × Int)) : Int × Int :=
  (start.1 + (isingDiagonalWalkDisplacement steps).1,
    start.2 + (isingDiagonalWalkDisplacement steps).2)


def IsingDiagonalWalkStepsValid (steps : List (Int × Int)) : Prop :=
  ∀ d ∈ steps, (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1)



structure IsingDiagonalWalkHitSplit (start : Int × Int) (level : Int) where
  before : List (Int × Int)
  after : List (Int × Int)
  hit : start.1 + (isingDiagonalWalkDisplacement before).1 = level

def isingDiagonalWalkNext (start d : Int × Int) : Int × Int :=
  (start.1 + d.1, start.2 + d.2)


def isingDiagonalWalkFirstHitSplit? (start : Int × Int) (level : Int) :
    (path : List (Int × Int)) → Option (IsingDiagonalWalkHitSplit start level)
  | [] =>
      if h : start.1 = level then
        some ⟨[], [], by simpa [isingDiagonalWalkDisplacement] using h⟩
      else none
  | d :: path =>
      if h : start.1 = level then
        some ⟨[], d :: path, by simpa [isingDiagonalWalkDisplacement] using h⟩
      else
        match isingDiagonalWalkFirstHitSplit? (isingDiagonalWalkNext start d)
            level path with
        | none => none
        | some w => some ⟨d :: w.before, w.after, by
            have hw := w.hit
            unfold isingDiagonalWalkNext isingDiagonalWalkDisplacement at hw
            simp only [isingDiagonalWalkDisplacement, List.map_cons,
              List.sum_cons]
            dsimp at hw ⊢
            omega⟩

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def steps (w : IsingDiagonalWalkHitSplit start level) : List (Int × Int) :=
  w.before ++ w.after

theorem firstHitSplit_steps {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    w.steps = path := by
  induction path generalizing start w with
  | nil =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        rfl
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        rfl
      · cases hrec : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path with
        | none => simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
        | some u =>
            simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
            subst w
            have hu := ih (start := isingDiagonalWalkNext start d)
              (w := u) hrec
            unfold steps at hu ⊢
            simp [hu]



def FirstHit (w : IsingDiagonalWalkHitSplit start level) : Prop :=
  ∀ k, k < w.before.length →
    (isingDiagonalWalkEndpoint start (w.before.take k)).1 ≠ level


theorem firstHitSplit_firstHit {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    w.FirstHit := by
  induction path generalizing start w with
  | nil =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        simp [FirstHit]
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
  | cons d path ih =>
      by_cases hs : start.1 = level
      · simp [isingDiagonalWalkFirstHitSplit?, hs] at h
        subst w
        simp [FirstHit]
      · cases hrec : isingDiagonalWalkFirstHitSplit?
            (isingDiagonalWalkNext start d) level path with
        | none => simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
        | some u =>
            simp [isingDiagonalWalkFirstHitSplit?, hs, hrec] at h
            subst w
            intro k hk
            cases k with
            | zero =>
                simpa [isingDiagonalWalkEndpoint,
                  isingDiagonalWalkDisplacement] using hs
            | succ k =>
                have hk' : k < u.before.length := by
                  simpa using hk
                have hu := ih (start := isingDiagonalWalkNext start d)
                  (w := u) hrec k hk'
                simpa [isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
                  isingDiagonalWalkDisplacement, add_assoc] using hu



theorem firstHitSplit_eq_some (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.FirstHit) :
    isingDiagonalWalkFirstHitSplit? start level w.steps = some w := by
  cases w with
  | mk before after hit =>
      induction before generalizing start with
      | nil =>
          have hs : start.1 = level := by
            simpa [isingDiagonalWalkDisplacement] using hit
          cases after <;> simp [steps, isingDiagonalWalkFirstHitSplit?, hs]
      | cons d before ih =>
          have hs : start.1 ≠ level := by
            have hzero := hw 0 (by simp)
            simpa [isingDiagonalWalkEndpoint,
              isingDiagonalWalkDisplacement] using hzero
          let u : IsingDiagonalWalkHitSplit
              (isingDiagonalWalkNext start d) level :=
            ⟨before, after, by
              unfold isingDiagonalWalkNext
              unfold isingDiagonalWalkDisplacement at hit ⊢
              simp only [List.map_cons, List.sum_cons] at hit ⊢
              omega⟩
          have hu : u.FirstHit := by
            intro k hk
            have hsucc := hw (k + 1) (by simpa using hk)
            simpa [u, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
              isingDiagonalWalkDisplacement, add_assoc] using hsucc
          have hrec : isingDiagonalWalkFirstHitSplit?
              (isingDiagonalWalkNext start d) level u.steps = some u :=
            ih (start := isingDiagonalWalkNext start d) u.hit hu
          simp [steps] at hrec
          simp [steps, isingDiagonalWalkFirstHitSplit?, hs, hrec, u]

def endpoint (w : IsingDiagonalWalkHitSplit start level) : Int × Int :=
  isingDiagonalWalkEndpoint start w.steps

def Valid (w : IsingDiagonalWalkHitSplit start level) : Prop :=
  IsingDiagonalWalkStepsValid w.steps

def reflectIncrement (d : Int × Int) : Int × Int :=
  (-d.1, d.2)


def reflect (w : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit start level where
  before := w.before
  after := w.after.map reflectIncrement
  hit := w.hit

@[simp] theorem reflect_before (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.before = w.before := rfl

@[simp] theorem reflect_after (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.after = w.after.map reflectIncrement := rfl

@[simp] theorem reflect_reflect (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.reflect = w := by
  cases w with
  | mk before after hit =>
      simp [reflect, reflectIncrement, Function.comp_def]


def reflectEquiv : IsingDiagonalWalkHitSplit start level ≃
    IsingDiagonalWalkHitSplit start level where
  toFun := reflect
  invFun := reflect
  left_inv := reflect_reflect
  right_inv := reflect_reflect

theorem reflect_length (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.steps.length = w.steps.length := by
  simp [steps, reflect]

theorem reflect_valid (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.Valid) : w.reflect.Valid := by
  unfold Valid IsingDiagonalWalkStepsValid at hw ⊢
  unfold steps at hw
  intro d hd
  simp only [steps, reflect, List.mem_append, List.mem_map] at hd
  rcases hd with hd | ⟨e, he, rfl⟩
  · exact hw d (List.mem_append.mpr (Or.inl hd))
  · have heValid := hw e (List.mem_append.mpr (Or.inr he))
    rcases heValid with ⟨hex, hey⟩
    constructor
    · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
    · simpa [reflectIncrement] using hey

theorem reflect_firstHit (w : IsingDiagonalWalkHitSplit start level)
    (hw : w.FirstHit) : w.reflect.FirstHit := by
  simpa [FirstHit] using hw

private theorem displacement_append (a b : List (Int × Int)) :
    isingDiagonalWalkDisplacement (a ++ b) =
      ((isingDiagonalWalkDisplacement a).1 + (isingDiagonalWalkDisplacement b).1,
        (isingDiagonalWalkDisplacement a).2 + (isingDiagonalWalkDisplacement b).2) := by
  simp [isingDiagonalWalkDisplacement, List.sum_append]

private theorem displacement_reflectSuffix (s : List (Int × Int)) :
    isingDiagonalWalkDisplacement (s.map reflectIncrement) =
      (-(isingDiagonalWalkDisplacement s).1,
        (isingDiagonalWalkDisplacement s).2) := by
  have hneg : (s.map (fun d ↦ -d.1)).sum =
      -(s.map Prod.fst).sum := by
    induction s with
    | nil => simp
    | cons d s ih => simp [ih, add_comm]
  unfold isingDiagonalWalkDisplacement
  simp only [List.map_map]
  change ((s.map (fun d ↦ (reflectIncrement d).1)).sum,
    (s.map (fun d ↦ (reflectIncrement d).2)).sum) = _
  simp only [reflectIncrement]
  rw [hneg]


theorem reflect_endpoint_fst (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.endpoint.1 = 2 * level - w.endpoint.1 := by
  rw [show w.reflect.endpoint.1 =
      start.1 + (isingDiagonalWalkDisplacement
        (w.before ++ w.after.map reflectIncrement)).1 by rfl]
  rw [displacement_append, displacement_reflectSuffix]
  unfold endpoint steps isingDiagonalWalkEndpoint
  rw [displacement_append]
  have hw := w.hit
  dsimp at hw ⊢
  omega


theorem reflect_endpoint_snd (w : IsingDiagonalWalkHitSplit start level) :
    w.reflect.endpoint.2 = w.endpoint.2 := by
  rw [show w.reflect.endpoint.2 =
      start.2 + (isingDiagonalWalkDisplacement
        (w.before ++ w.after.map reflectIncrement)).2 by rfl]
  rw [displacement_append, displacement_reflectSuffix]
  unfold endpoint steps isingDiagonalWalkEndpoint
  rw [displacement_append]


def reflectedEndpoint (level : Int) (target : Int × Int) : Int × Int :=
  (2 * level - target.1, target.2)

@[simp] theorem reflectedEndpoint_reflectedEndpoint (level : Int)
    (target : Int × Int) :
    reflectedEndpoint level (reflectedEndpoint level target) = target := by
  unfold reflectedEndpoint
  ext <;> simp



def FirstHitFamily (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :=
  {w : IsingDiagonalWalkHitSplit start level //
    w.FirstHit ∧ w.Valid ∧ w.steps.length = walkLength ∧ w.endpoint = target}

private def reflectFirstHitFamily
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    FirstHitFamily start level walkLength target →
      FirstHitFamily start level walkLength (reflectedEndpoint level target) :=
  fun w ↦ ⟨w.1.reflect, reflect_firstHit w.1 w.2.1,
    reflect_valid w.1 w.2.2.1, by
      rw [reflect_length]
      exact w.2.2.2.1, by
      apply Prod.ext
      · rw [reflect_endpoint_fst, w.2.2.2.2]
        rfl
      · rw [reflect_endpoint_snd, w.2.2.2.2]
        rfl⟩

private def reflectFirstHitFamilyBack
    {start : Int × Int} {level : Int} {walkLength : Nat}
    {target : Int × Int} :
    FirstHitFamily start level walkLength (reflectedEndpoint level target) →
      FirstHitFamily start level walkLength target :=
  fun w ↦ ⟨w.1.reflect, reflect_firstHit w.1 w.2.1,
    reflect_valid w.1 w.2.2.1, by
      rw [reflect_length]
      exact w.2.2.2.1, by
      apply Prod.ext
      · rw [reflect_endpoint_fst, w.2.2.2.2]
        unfold reflectedEndpoint
        dsimp
        omega
      · rw [reflect_endpoint_snd, w.2.2.2.2]
        rfl⟩



def reflectFirstHitFamilyEquiv
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    FirstHitFamily start level walkLength target ≃
      FirstHitFamily start level walkLength (reflectedEndpoint level target) where
  toFun := reflectFirstHitFamily
  invFun := reflectFirstHitFamilyBack
  left_inv w := by
    apply Subtype.ext
    simp [reflectFirstHitFamily, reflectFirstHitFamilyBack]
  right_inv w := by
    apply Subtype.ext
    simp [reflectFirstHitFamily, reflectFirstHitFamilyBack]

theorem natCard_firstHitFamily_eq_reflected
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.card (FirstHitFamily start level walkLength target) =
      Nat.card (FirstHitFamily start level walkLength
        (reflectedEndpoint level target)) :=
  Nat.card_congr (reflectFirstHitFamilyEquiv start level walkLength target)


noncomputable def firstHitFamilyWeight
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) : Real :=
  Nat.card (FirstHitFamily start level walkLength target) /
    4 ^ walkLength


theorem firstHitFamilyWeight_eq_reflected
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    firstHitFamilyWeight start level walkLength target =
      firstHitFamilyWeight start level walkLength
        (reflectedEndpoint level target) := by
  unfold firstHitFamilyWeight
  rw [natCard_firstHitFamily_eq_reflected]



theorem firstHitSplit_reflect {path : List (Int × Int)}
    {w : IsingDiagonalWalkHitSplit start level}
    (h : isingDiagonalWalkFirstHitSplit? start level path = some w) :
    isingDiagonalWalkFirstHitSplit? start level w.reflect.steps =
      some w.reflect :=
  firstHitSplit_eq_some w.reflect (reflect_firstHit w
    (firstHitSplit_firstHit h))

end IsingDiagonalWalkHitSplit






noncomputable def isingLeapfrogKilledPathCount (R : Nat) :
    Nat → IsingLeapfrogBox R → IsingLeapfrogBox R → Nat
  | 0, p, q =>
      if isingLeapfrogBoxBoundary R q then 0 else if p = q then 1 else 0
  | t + 1, p, q =>
      if isingLeapfrogBoxBoundary R q then 0
      else if hp : isingLeapfrogBoxBoundary R p then
        4 * isingLeapfrogKilledPathCount R t p q
      else
        isingLeapfrogKilledPathCount R t (isingLeapfrogSW R p) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogNE R p hp) q


theorem isingLeapfrogKilledKernel_eq_pathCount_div (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q =
      isingLeapfrogKilledPathCount R t p q / (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      simp [isingLeapfrogKilledKernel, isingLeapfrogKilledPathCount,
        isingLeapfrogStoppedKernel]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · simp [isingLeapfrogKilledKernel, isingLeapfrogKilledPathCount, hq]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · have ihp := ih p
          simp only [isingLeapfrogKilledKernel, if_neg hq] at ihp
          simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_pos hp,
            isingLeapfrogKilledPathCount]
          rw [ihp]
          push_cast
          rw [pow_succ]
          ring
        · simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogKilledPathCount]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [hSW, hSE, hNW, hNE]
          push_cast
          rw [pow_succ]
          ring



noncomputable def isingLeapfrogStoppedOneStepCount (R : Nat)
    (p q : IsingLeapfrogBox R) : Nat :=
  if hp : isingLeapfrogBoxBoundary R p then
    if p = q then 4 else 0
  else
    (if isingLeapfrogSW R p = q then 1 else 0) +
      (if isingLeapfrogSE R p hp = q then 1 else 0) +
      (if isingLeapfrogNW R p hp = q then 1 else 0) +
      (if isingLeapfrogNE R p hp = q then 1 else 0)

theorem isingLeapfrogStoppedKernel_one_eq_pathCount_div (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R 1 p q =
      isingLeapfrogStoppedOneStepCount R p q / 4 := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp only [isingLeapfrogStoppedKernel, dif_pos hp]
    unfold isingLeapfrogStoppedOneStepCount
    rw [dif_pos hp]
    by_cases hpq : p = q <;> simp [hpq]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    unfold isingLeapfrogStoppedOneStepCount
    rw [dif_neg hp]
    push_cast
    congr



theorem isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div
    (R t : Nat) (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q =
      (isingLeapfrogKilledPathCount R t p r *
          isingLeapfrogStoppedOneStepCount R r q : Nat) /
        (4 : Real) ^ (t + 1) := by
  rw [isingLeapfrogKilledKernel_eq_pathCount_div,
    isingLeapfrogStoppedKernel_one_eq_pathCount_div]
  push_cast
  rw [pow_succ]
  ring




def isingLeapfrogBoxReflectX (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (⟨R - p.1.1, by omega⟩, p.2)

@[simp] theorem isingLeapfrogBoxReflectX_involutive (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxReflectX R (isingLeapfrogBoxReflectX R p) = p := by
  apply Prod.ext
  · apply Fin.ext
    simp [isingLeapfrogBoxReflectX]
    omega
  · rfl

@[simp] theorem isingLeapfrogBoxReflectX_eq_iff (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogBoxReflectX R p = isingLeapfrogBoxReflectX R q ↔ p = q :=
  (Function.Involutive.injective
    (isingLeapfrogBoxReflectX_involutive R)).eq_iff

theorem isingLeapfrogBoxBoundary_reflectX_iff (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxBoundary R (isingLeapfrogBoxReflectX R p) ↔
      isingLeapfrogBoxBoundary R p := by
  unfold isingLeapfrogBoxBoundary isingLeapfrogBoxReflectX
  dsimp
  omega

private theorem isingLeapfrogBoxReflectX_SW (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogSW R p) =
      isingLeapfrogSE R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogSouth]

private theorem isingLeapfrogBoxReflectX_SE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogSE R p hp) =
      isingLeapfrogSW R (isingLeapfrogBoxReflectX R p) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogSW, isingLeapfrogSE,
      isingLeapfrogSouth]

private theorem isingLeapfrogBoxReflectX_NW (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogNW R p hp) =
      isingLeapfrogNE R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogNorth]

private theorem isingLeapfrogBoxReflectX_NE (R : Nat)
    (p : IsingLeapfrogBox R) (hp : ¬ isingLeapfrogBoxBoundary R p) :
    isingLeapfrogBoxReflectX R (isingLeapfrogNE R p hp) =
      isingLeapfrogNW R (isingLeapfrogBoxReflectX R p)
        (mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp) := by
  apply Prod.ext <;> apply Fin.ext
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogWest, isingLeapfrogEast]
    unfold isingLeapfrogBoxBoundary at hp
    omega
  · simp [isingLeapfrogBoxReflectX, isingLeapfrogNW, isingLeapfrogNE,
      isingLeapfrogNorth]



theorem isingLeapfrogKilledPathCount_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledPathCount R t p q := by
  induction t generalizing p with
  | zero =>
      simp only [isingLeapfrogKilledPathCount]
      rw [if_congr (isingLeapfrogBoxBoundary_reflectX_iff R q) rfl rfl]
      simp
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hqr := (isingLeapfrogBoxBoundary_reflectX_iff R q).2 hq
        simp [isingLeapfrogKilledPathCount, hq, hqr]
      · have hqr : ¬ isingLeapfrogBoxBoundary R
            (isingLeapfrogBoxReflectX R q) :=
          mt (isingLeapfrogBoxBoundary_reflectX_iff R q).mp hq
        by_cases hp : isingLeapfrogBoxBoundary R p
        · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
          simp [isingLeapfrogKilledPathCount, hq, hqr, hp, hpr, ih]
        · have hpr : ¬ isingLeapfrogBoxBoundary R
              (isingLeapfrogBoxReflectX R p) :=
            mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
          simp only [isingLeapfrogKilledPathCount, hq, hqr,
            dif_neg hp, dif_neg hpr]
          rw [← isingLeapfrogBoxReflectX_SE R p hp,
            ← isingLeapfrogBoxReflectX_SW R p hp,
            ← isingLeapfrogBoxReflectX_NE R p hp,
            ← isingLeapfrogBoxReflectX_NW R p hp]
          rw [ih, ih, ih, ih]
          simp [add_comm, add_left_comm]

theorem isingLeapfrogStoppedOneStepCount_reflectX (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogStoppedOneStepCount R p q := by
  by_cases hp : isingLeapfrogBoxBoundary R p
  · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
    simp only [isingLeapfrogStoppedOneStepCount, dif_pos hp, dif_pos hpr]
    simp
  · have hpr : ¬ isingLeapfrogBoxBoundary R
        (isingLeapfrogBoxReflectX R p) :=
      mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
    simp only [isingLeapfrogStoppedOneStepCount, dif_neg hp, dif_neg hpr]
    rw [← isingLeapfrogBoxReflectX_SE R p hp,
      ← isingLeapfrogBoxReflectX_SW R p hp,
      ← isingLeapfrogBoxReflectX_NE R p hp,
      ← isingLeapfrogBoxReflectX_NW R p hp]
    simp [add_comm, add_left_comm]



theorem isingLeapfrogFirstHitFluxNumerator_reflectX (R t : Nat)
    (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledPathCount R t (isingLeapfrogBoxReflectX R p)
          (isingLeapfrogBoxReflectX R r) *
        isingLeapfrogStoppedOneStepCount R (isingLeapfrogBoxReflectX R r)
          (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledPathCount R t p r *
        isingLeapfrogStoppedOneStepCount R r q := by
  rw [isingLeapfrogKilledPathCount_reflectX,
    isingLeapfrogStoppedOneStepCount_reflectX]


theorem isingLeapfrogFirstHitFluxSummand_reflectX (R t : Nat)
    (p r q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t (isingLeapfrogBoxReflectX R p)
          (isingLeapfrogBoxReflectX R r) *
        isingLeapfrogStoppedKernel R 1 (isingLeapfrogBoxReflectX R r)
          (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogKilledKernel R t p r *
        isingLeapfrogStoppedKernel R 1 r q := by
  rw [isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div,
    isingLeapfrogKilled_mul_stopped_one_eq_pathCount_div,
    isingLeapfrogFirstHitFluxNumerator_reflectX]

theorem isingLeapfrogStoppedKernel_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogStoppedKernel R t p q := by
  induction t generalizing p with
  | zero => simp [isingLeapfrogStoppedKernel]
  | succ t ih =>
      by_cases hp : isingLeapfrogBoxBoundary R p
      · have hpr := (isingLeapfrogBoxBoundary_reflectX_iff R p).2 hp
        simp only [isingLeapfrogStoppedKernel, dif_pos hp, dif_pos hpr]
        exact ih p
      · have hpr : ¬ isingLeapfrogBoxBoundary R
            (isingLeapfrogBoxReflectX R p) :=
          mt (isingLeapfrogBoxBoundary_reflectX_iff R p).mp hp
        simp only [isingLeapfrogStoppedKernel, dif_neg hp, dif_neg hpr]
        rw [← isingLeapfrogBoxReflectX_SE R p hp,
          ← isingLeapfrogBoxReflectX_SW R p hp,
          ← isingLeapfrogBoxReflectX_NE R p hp,
          ← isingLeapfrogBoxReflectX_NW R p hp]
        rw [ih, ih, ih, ih]
        ring


theorem isingLeapfrogExitKernel_reflectX (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogExitKernel R t (isingLeapfrogBoxReflectX R p)
        (isingLeapfrogBoxReflectX R q) =
      isingLeapfrogExitKernel R t p q := by
  unfold isingLeapfrogExitKernel
  rw [if_congr (isingLeapfrogBoxBoundary_reflectX_iff R q) rfl rfl]
  split_ifs
  · exact isingLeapfrogStoppedKernel_reflectX R t p q
  · rfl





theorem isingLeapfrogDiagonalAdjacent_eq_neighbor {R : Nat}
    (p p' : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    p = isingLeapfrogSW R p' ∨
      p = isingLeapfrogSE R p' hp' ∨
      p = isingLeapfrogNW R p' hp' ∨
      p = isingLeapfrogNE R p' hp' := by
  rcases hpp' with ⟨hx, hy⟩
  unfold Nat.dist at hx hy
  have hx' : p.1.1 + 1 = p'.1.1 ∨ p'.1.1 + 1 = p.1.1 := by omega
  have hy' : p.2.1 + 1 = p'.2.1 ∨ p'.2.1 + 1 = p.2.1 := by omega
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogSW, isingLeapfrogWest]
      omega
    · simp [isingLeapfrogSW, isingLeapfrogSouth]
      omega
  · right; right; left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogNW, isingLeapfrogWest]
      omega
    · simp [isingLeapfrogNW, isingLeapfrogNorth]
      omega
  · right; left
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogSE, isingLeapfrogEast]
      omega
    · simp [isingLeapfrogSE, isingLeapfrogSouth]
      omega
  · right; right; right
    apply Prod.ext <;> apply Fin.ext
    · simp [isingLeapfrogNE, isingLeapfrogEast]
      omega
    · simp [isingLeapfrogNE, isingLeapfrogNorth]
      omega



theorem isingLeapfrogExitKernel_neighbor_timeOffset_eq (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    isingLeapfrogExitKernel R (t + 1) p' q -
        isingLeapfrogExitKernel R t p q =
      ((isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogExitKernel R t p q) +
        (isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogExitKernel R t p q)) / 4 := by
  rw [isingLeapfrogExitKernel_succ]
  simp only [dif_neg hp']
  ring

theorem isingLeapfrogExitKernel_neighbor_timeOffset_abs_le (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    |isingLeapfrogExitKernel R (t + 1) p' q -
        isingLeapfrogExitKernel R t p q| ≤
      (|isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogExitKernel R t p q| +
        |isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogExitKernel R t p q|) / 4 := by
  rw [isingLeapfrogExitKernel_neighbor_timeOffset_eq R t p p' q hp']
  rw [abs_div]
  norm_num
  apply div_le_div_of_nonneg_right _ (by norm_num)
  let a := isingLeapfrogExitKernel R t (isingLeapfrogSW R p') q -
    isingLeapfrogExitKernel R t p q
  let b := isingLeapfrogExitKernel R t (isingLeapfrogSE R p' hp') q -
    isingLeapfrogExitKernel R t p q
  let c := isingLeapfrogExitKernel R t (isingLeapfrogNW R p' hp') q -
    isingLeapfrogExitKernel R t p q
  let d := isingLeapfrogExitKernel R t (isingLeapfrogNE R p' hp') q -
    isingLeapfrogExitKernel R t p q
  change |a + b + c + d| ≤ |a| + |b| + |c| + |d|
  have hab := abs_add_le a b
  have habc := abs_add_le (a + b) c
  have habcd := abs_add_le (a + b + c) d
  linarith


theorem isingLeapfrogStoppedKernel_neighbor_timeOffset_eq (R t : Nat)
    (p p' q : IsingLeapfrogBox R)
    (hp' : ¬ isingLeapfrogBoxBoundary R p') :
    isingLeapfrogStoppedKernel R (t + 1) p' q -
        isingLeapfrogStoppedKernel R t p q =
      ((isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p' hp') q -
          isingLeapfrogStoppedKernel R t p q) +
        (isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p' hp') q -
          isingLeapfrogStoppedKernel R t p q)) / 4 := by
  rw [isingLeapfrogStoppedKernel_succ]
  simp only [dif_neg hp']
  ring



namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}



def reflectPrefix (w : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level where
  before := w.before.map reflectIncrement
  after := w.after
  hit := by
    rw [displacement_reflectSuffix]
    unfold reflectedEndpoint
    have hw := w.hit
    dsimp at hw ⊢
    omega

@[simp] theorem reflectPrefix_before
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.before = w.before.map reflectIncrement := rfl

@[simp] theorem reflectPrefix_after
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.after = w.after := rfl

theorem reflectPrefix_length
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.steps.length = w.steps.length := by
  simp [reflectPrefix, steps]

theorem reflectPrefix_valid
    (w : IsingDiagonalWalkHitSplit start level) (hw : w.Valid) :
    w.reflectPrefix.Valid := by
  unfold Valid IsingDiagonalWalkStepsValid at hw ⊢
  intro d hd
  simp only [steps, reflectPrefix, List.mem_append, List.mem_map] at hd
  rcases hd with ⟨e, he, rfl⟩ | hd
  · have heValid := hw e (by
      unfold steps
      exact List.mem_append.mpr (Or.inl he))
    rcases heValid with ⟨hex, hey⟩
    constructor
    · rcases hex with hex | hex <;> simp [reflectIncrement, hex]
    · simpa [reflectIncrement] using hey
  · exact hw d (by
      unfold steps
      exact List.mem_append.mpr (Or.inr hd))


theorem reflectPrefix_firstHit
    (w : IsingDiagonalWalkHitSplit start level) (hw : w.FirstHit) :
    w.reflectPrefix.FirstHit := by
  intro k hk
  have hk' : k < w.before.length := by simpa using hk
  have hbefore := hw k hk'
  simp only [reflectPrefix_before]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint at hbefore ⊢
  rw [displacement_reflectSuffix]
  unfold reflectedEndpoint
  dsimp at hbefore ⊢
  omega


theorem reflectPrefix_endpoint_take_fst_of_le_before
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : k ≤ w.before.length) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k)).1 =
      2 * level -
        (isingDiagonalWalkEndpoint start (w.steps.take k)).1 := by
  have hmap : k ≤ (w.before.map reflectIncrement).length := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append_of_le_length hk,
    List.take_append_of_le_length hmap]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint
  rw [displacement_reflectSuffix]
  unfold reflectedEndpoint
  dsimp
  ring


theorem reflectPrefix_endpoint_take_snd_of_le_before
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : k ≤ w.before.length) :
    (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k)).2 =
      (isingDiagonalWalkEndpoint start (w.steps.take k)).2 := by
  have hmap : k ≤ (w.before.map reflectIncrement).length := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append_of_le_length hk,
    List.take_append_of_le_length hmap]
  rw [← List.map_take]
  unfold isingDiagonalWalkEndpoint
  rw [displacement_reflectSuffix]
  rfl


theorem reflectPrefix_endpoint_fst
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint.1 = w.endpoint.1 := by
  unfold endpoint steps isingDiagonalWalkEndpoint reflectPrefix
  rw [displacement_append, displacement_append,
    displacement_reflectSuffix]
  unfold reflectedEndpoint
  have hw := w.hit
  dsimp at hw ⊢
  omega


theorem reflectPrefix_endpoint_snd
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint.2 = w.endpoint.2 := by
  change (reflectedEndpoint level start).2 +
      (isingDiagonalWalkDisplacement
        (w.before.map reflectIncrement ++ w.after)).2 =
    start.2 +
      (isingDiagonalWalkDisplacement (w.before ++ w.after)).2
  rw [displacement_append, displacement_append,
    displacement_reflectSuffix]
  rfl

theorem reflectPrefix_endpoint
    (w : IsingDiagonalWalkHitSplit start level) :
    w.reflectPrefix.endpoint = w.endpoint := by
  apply Prod.ext
  · exact reflectPrefix_endpoint_fst w
  · exact reflectPrefix_endpoint_snd w

private def unreflectPrefix
    (w : IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level) :
    IsingDiagonalWalkHitSplit start level where
  before := w.before.map reflectIncrement
  after := w.after
  hit := by
    rw [displacement_reflectSuffix]
    have hw := w.hit
    unfold reflectedEndpoint at hw
    dsimp at hw ⊢
    omega

@[simp] theorem unreflectPrefix_reflectPrefix
    (w : IsingDiagonalWalkHitSplit start level) :
    unreflectPrefix w.reflectPrefix = w := by
  cases w with
  | mk before after hit =>
      simp [unreflectPrefix, reflectPrefix, reflectIncrement,
        Function.comp_def]

@[simp] theorem reflectPrefix_unreflectPrefix
    (w : IsingDiagonalWalkHitSplit (reflectedEndpoint level start) level) :
    (unreflectPrefix w).reflectPrefix = w := by
  cases w with
  | mk before after hit =>
      simp [unreflectPrefix, reflectPrefix, reflectIncrement,
        Function.comp_def]

private def reflectPrefixFirstHitFamily
    {walkLength : Nat} {target : Int × Int} :
    FirstHitFamily start level walkLength target →
      FirstHitFamily (reflectedEndpoint level start) level walkLength target :=
  fun w ↦ ⟨w.1.reflectPrefix, reflectPrefix_firstHit w.1 w.2.1,
    reflectPrefix_valid w.1 w.2.2.1, by
      rw [reflectPrefix_length]
      exact w.2.2.2.1, by
      rw [reflectPrefix_endpoint]
      exact w.2.2.2.2⟩

private def unreflectPrefixFirstHitFamily
    {walkLength : Nat} {target : Int × Int} :
    FirstHitFamily (reflectedEndpoint level start) level walkLength target →
      FirstHitFamily start level walkLength target :=
  fun w ↦ ⟨unreflectPrefix w.1, by
      have h := reflectPrefix_firstHit w.1 w.2.1
      simpa [unreflectPrefix, reflectPrefix, FirstHit,
        reflectedEndpoint] using h, by
      have h := reflectPrefix_valid w.1 w.2.2.1
      simpa [unreflectPrefix, reflectPrefix, Valid, steps] using h, by
      simpa [unreflectPrefix, reflectPrefix, steps] using w.2.2.2.1, by
      have h := reflectPrefix_endpoint w.1
      simpa [unreflectPrefix, reflectPrefix, endpoint, steps,
        reflectedEndpoint] using h.trans w.2.2.2.2⟩



def reflectPrefixFirstHitFamilyEquiv
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    FirstHitFamily start level walkLength target ≃
      FirstHitFamily (reflectedEndpoint level start) level walkLength target where
  toFun := reflectPrefixFirstHitFamily
  invFun := unreflectPrefixFirstHitFamily
  left_inv w := by
    apply Subtype.ext
    exact unreflectPrefix_reflectPrefix w.1
  right_inv w := by
    apply Subtype.ext
    exact reflectPrefix_unreflectPrefix w.1

theorem natCard_firstHitFamily_eq_mirroredStart
    (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.card (FirstHitFamily start level walkLength target) =
      Nat.card (FirstHitFamily (reflectedEndpoint level start) level
        walkLength target) :=
  Nat.card_congr
    (reflectPrefixFirstHitFamilyEquiv start level walkLength target)


def InOpenBox (R : Nat) (z : Int × Int) : Prop :=
  0 < z.1 ∧ z.1 < R ∧ 0 < z.2 ∧ z.2 < R



def StaysInOpenBox (R : Nat) (start : Int × Int)
    (path : List (Int × Int)) : Prop :=
  ∀ k, k ≤ path.length →
    InOpenBox R (isingDiagonalWalkEndpoint start (path.take k))

private theorem reflectPrefix_endpoint_take_eq_of_before_length_le
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : w.before.length ≤ k) :
    isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k) =
      isingDiagonalWalkEndpoint start (w.steps.take k) := by
  have hmap : (w.before.map reflectIncrement).length ≤ k := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append]
  rw [List.take_of_length_le hk, List.take_of_length_le hmap]
  have hsub : k - (w.before.map reflectIncrement).length =
      k - w.before.length := by simp
  rw [hsub]
  apply Prod.ext
  · unfold isingDiagonalWalkEndpoint
    rw [displacement_append, displacement_append,
      displacement_reflectSuffix]
    unfold reflectedEndpoint
    have hw := w.hit
    dsimp at hw ⊢
    omega
  · unfold isingDiagonalWalkEndpoint
    rw [displacement_append, displacement_append,
      displacement_reflectSuffix]
    unfold reflectedEndpoint
    rfl



theorem survivalException_before_firstHit
    (w : IsingDiagonalWalkHitSplit start level)
    {R : Nat}
    (hs : StaysInOpenBox R start w.steps)
    (hr : ¬ StaysInOpenBox R (reflectedEndpoint level start)
      w.reflectPrefix.steps) :
    ∃ k, k < w.before.length ∧ k ≤ w.reflectPrefix.steps.length ∧
      ¬ InOpenBox R (isingDiagonalWalkEndpoint
        (reflectedEndpoint level start) (w.reflectPrefix.steps.take k)) := by
  classical
  unfold StaysInOpenBox at hr
  push Not at hr
  rcases hr with ⟨k, hk, hout⟩
  refine ⟨k, ?_, hk, hout⟩
  by_contra hnot
  have hbefore : w.before.length ≤ k := by omega
  have hk' : k ≤ w.steps.length := by
    rw [← reflectPrefix_length w]
    exact hk
  have hin := hs k hk'
  rw [reflectPrefix_endpoint_take_eq_of_before_length_le w k hbefore] at hout
  exact hout hin



theorem exists_prefix_fst_eq_of_lt_of_le
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstart : start.1 < level)
    (hend : level ≤ (isingDiagonalWalkEndpoint start path).1) :
    ∃ k, k ≤ path.length ∧
      (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
  induction path generalizing start with
  | nil =>
      simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement] at hend
      omega
  | cons d path ih =>
      have hd := hvalid d (by simp)
      let next := isingDiagonalWalkNext start d
      have hendpoint : isingDiagonalWalkEndpoint next path =
          isingDiagonalWalkEndpoint start (d :: path) := by
        unfold next isingDiagonalWalkNext isingDiagonalWalkEndpoint
          isingDiagonalWalkDisplacement
        apply Prod.ext <;> simp <;> ring
      by_cases hnext : next.1 = level
      · exact ⟨1, by simp, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement] using hnext⟩
      · have hnextlt : next.1 < level := by
          unfold next isingDiagonalWalkNext at hnext ⊢
          rcases hd.1 with hd | hd <;> omega
        have htailValid : IsingDiagonalWalkStepsValid path := by
          intro e he
          exact hvalid e (by simp [he])
        have htailEnd : level ≤ (isingDiagonalWalkEndpoint next path).1 := by
          rw [hendpoint]
          exact hend
        rcases ih next htailValid hnextlt htailEnd with ⟨k, hk, heq⟩
        exact ⟨k + 1, by simp; omega, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement, add_assoc] using heq⟩



theorem exists_prefix_fst_eq_of_ge_of_gt
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstart : level < start.1)
    (hend : (isingDiagonalWalkEndpoint start path).1 ≤ level) :
    ∃ k, k ≤ path.length ∧
      (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
  induction path generalizing start with
  | nil =>
      simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement] at hend
      omega
  | cons d path ih =>
      have hd := hvalid d (by simp)
      let next := isingDiagonalWalkNext start d
      have hendpoint : isingDiagonalWalkEndpoint next path =
          isingDiagonalWalkEndpoint start (d :: path) := by
        unfold next isingDiagonalWalkNext isingDiagonalWalkEndpoint
          isingDiagonalWalkDisplacement
        apply Prod.ext <;> simp <;> ring
      by_cases hnext : next.1 = level
      · exact ⟨1, by simp, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement] using hnext⟩
      · have hnextgt : level < next.1 := by
          unfold next isingDiagonalWalkNext at hnext ⊢
          rcases hd.1 with hd | hd <;> omega
        have htailValid : IsingDiagonalWalkStepsValid path := by
          intro e he
          exact hvalid e (by simp [he])
        have htailEnd : (isingDiagonalWalkEndpoint next path).1 ≤ level := by
          rw [hendpoint]
          exact hend
        rcases ih next htailValid hnextgt htailEnd with ⟨k, hk, heq⟩
        exact ⟨k + 1, by simp; omega, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement, add_assoc] using heq⟩



theorem FirstHit.endpoint_take_fst_lt
    (w : IsingDiagonalWalkHitSplit start level)
    (hfirst : w.FirstHit) (hvalid : w.Valid)
    (hstart : start.1 < level) (k : Nat) (hk : k < w.before.length) :
    (isingDiagonalWalkEndpoint start (w.before.take k)).1 < level := by
  by_contra hnot
  have hend : level ≤
      (isingDiagonalWalkEndpoint start (w.before.take k)).1 := by omega
  have htakeValid : IsingDiagonalWalkStepsValid (w.before.take k) := by
    intro d hd
    apply hvalid d
    unfold steps
    exact List.mem_append.mpr (Or.inl (List.mem_of_mem_take hd))
  rcases exists_prefix_fst_eq_of_lt_of_le (w.before.take k) start level
      htakeValid hstart hend with ⟨j, hj, heq⟩
  have hjk : j ≤ k := by
    rw [List.length_take] at hj
    omega
  have hjbefore : j < w.before.length := by omega
  have hno := hfirst j hjbefore
  apply hno
  simpa [List.take_take, Nat.min_eq_left hjk] using heq



theorem FirstHit.endpoint_take_fst_gt
    (w : IsingDiagonalWalkHitSplit start level)
    (hfirst : w.FirstHit) (hvalid : w.Valid)
    (hstart : level < start.1) (k : Nat) (hk : k < w.before.length) :
    level < (isingDiagonalWalkEndpoint start (w.before.take k)).1 := by
  by_contra hnot
  have hend :
      (isingDiagonalWalkEndpoint start (w.before.take k)).1 ≤ level := by
    omega
  have htakeValid : IsingDiagonalWalkStepsValid (w.before.take k) := by
    intro d hd
    apply hvalid d
    unfold steps
    exact List.mem_append.mpr (Or.inl (List.mem_of_mem_take hd))
  rcases exists_prefix_fst_eq_of_ge_of_gt (w.before.take k) start level
      htakeValid hstart hend with ⟨j, hj, heq⟩
  have hjk : j ≤ k := by
    rw [List.length_take] at hj
    omega
  have hjbefore : j < w.before.length := by omega
  have hno := hfirst j hjbefore
  apply hno
  simpa [List.take_take, Nat.min_eq_left hjk] using heq



def SurvivalMatchedFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily start level walkLength target //
    StaysInOpenBox R start w.1.steps ∧
      StaysInOpenBox R (reflectedEndpoint level start)
        w.1.reflectPrefix.steps}


def SurvivalMatchedMirrorFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily (reflectedEndpoint level start) level walkLength target //
    StaysInOpenBox R (reflectedEndpoint level start) w.1.steps ∧
      StaysInOpenBox R start (unreflectPrefix w.1).steps}




def survivalMatchedFirstHitFamilyEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivalMatchedFirstHitFamily R start level walkLength target ≃
      SurvivalMatchedMirrorFamily R start level walkLength target where
  toFun w := ⟨reflectPrefixFirstHitFamily w.1, w.2.2, by
    simpa [reflectPrefixFirstHitFamily, unreflectPrefixFirstHitFamily] using
      w.2.1⟩
  invFun w := ⟨unreflectPrefixFirstHitFamily w.1, w.2.2, by
    simpa [reflectPrefixFirstHitFamily, unreflectPrefixFirstHitFamily] using
      w.2.1⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact unreflectPrefix_reflectPrefix w.1.1
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact reflectPrefix_unreflectPrefix w.1.1

theorem natCard_survivalMatchedFirstHitFamily_eq
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.card (SurvivalMatchedFirstHitFamily R start level walkLength target) =
      Nat.card (SurvivalMatchedMirrorFamily R start level walkLength target) :=
  Nat.card_congr
    (survivalMatchedFirstHitFamilyEquiv R start level walkLength target)


def SurvivingFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : FirstHitFamily start level walkLength target //
    StaysInOpenBox R start w.1.steps}


def SurvivalExceptionalFirstHitFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : SurvivingFirstHitFamily R start level walkLength target //
    ¬ StaysInOpenBox R (reflectedEndpoint level start)
      w.1.1.reflectPrefix.steps}



def SurvivalExceptionalMirrorFamily (R : Nat) (start : Int × Int)
    (level : Int) (walkLength : Nat) (target : Int × Int) :=
  {w : SurvivingFirstHitFamily R (reflectedEndpoint level start) level
      walkLength target //
    ¬ StaysInOpenBox R start (unreflectPrefix w.1.1).steps}



noncomputable def survivingFirstHitFamilyPartitionEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivingFirstHitFamily R start level walkLength target ≃
      SurvivalMatchedFirstHitFamily R start level walkLength target ⊕
        SurvivalExceptionalFirstHitFamily R start level walkLength target where
  toFun w := by
    classical
    exact if h : StaysInOpenBox R (reflectedEndpoint level start)
        w.1.1.reflectPrefix.steps then
        Sum.inl ⟨w.1, w.2, h⟩
      else Sum.inr ⟨w, h⟩
  invFun
    | Sum.inl w => ⟨w.1, w.2.1⟩
    | Sum.inr w => w.1
  left_inv w := by
    classical
    dsimp
    split_ifs <;> apply Subtype.ext <;> rfl
  right_inv w := by
    classical
    rcases w with w | w
    · simp only
      rw [dif_pos w.2.2]
      congr 1
    · simp only
      rw [dif_neg w.2]
      congr 1



noncomputable def survivingMirrorFamilyPartitionEquiv
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    SurvivingFirstHitFamily R (reflectedEndpoint level start) level
        walkLength target ≃
      SurvivalMatchedMirrorFamily R start level walkLength target ⊕
        SurvivalExceptionalMirrorFamily R start level walkLength target where
  toFun w := by
    classical
    exact if h : StaysInOpenBox R start (unreflectPrefix w.1.1).steps then
        Sum.inl ⟨w.1, w.2, h⟩
      else Sum.inr ⟨w, h⟩
  invFun
    | Sum.inl w => ⟨w.1, w.2.1⟩
    | Sum.inr w => w.1
  left_inv w := by
    classical
    dsimp
    split_ifs <;> apply Subtype.ext <;> rfl
  right_inv w := by
    classical
    rcases w with w | w
    · simp only
      rw [dif_pos w.2.2]
      congr 1
    · simp only
      rw [dif_neg w.2]
      congr 1

end IsingDiagonalWalkHitSplit

end StatMech.Universality

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorSign

/-! # Fused runs of monomial letters in packed tensor words

A run of monomial letters acts on a packed tensor by one relabeling of the spin labels, one phase
mask and one permutation of the columns.  `tensorRun w ls S X` applies the run `ls` with a short
transvection list `S` for the composite relabeling (checked against the concatenated letter lists
on the twelve basis labels by `runOk`), the composite phase mask `runMask w ls` (folded over the
letters on one packed number) and the composite column map `runCol ls`.  Plans of letters and runs
(`TPlan`), evaluated by `tensorPlan`, have the genuine tensor action of the expanded word
(`tensorPlan_actual`) and the same rational tensor as `tensorWordAll` (`tensorPlan_rat`).  A run
of `m` letters costs one letter's column work instead of `m`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators
set_option autoImplicit false

/-! ## Composite data of a run -/

/-- The concatenated relabeling list of a run (the head letter acts last). -/
def runOps : List (Fin 2 × Bool) → List IdxOp
  | [] => []
  | l :: ls => runOps ls ++ monoOps (monoIdx l)

/-- The source column of output column `i` under a run. -/
def runCol : List (Fin 2 × Bool) → ℕ → ℕ
  | [], i => i
  | l :: ls, i => runCol ls ((monoCols (monoIdx l)).getD i 0)

/-- The phase of a run at a spin label. -/
def runPhase : List (Fin 2 × Bool) → ℕ → Bool
  | [], _ => false
  | l :: ls, k =>
    decide (monoPhaseAt (monoIdx l) k = 1) ^^ runPhase ls (idxOps (monoOps (monoIdx l)) k)

/-- The phase mask of a run, folded over the letters on one packed number. -/
def runMask (w : ℕ) : List (Fin 2 × Bool) → ℕ
  | [] => 0
  | l :: ls => monoPhaseMask w (monoIdx l) ^^^ actOps w 12 (monoOps (monoIdx l)) (runMask w ls)

/-- The composite images of the twelve basis labels under a run, composed letter by letter. -/
def runImgs : List (Fin 2 × Bool) → List ℕ
  | [] => (List.range 12).map (fun j => 2 ^ j)
  | l :: ls => (List.range 12).map (fun j =>
      linFold (fun i => (runImgs ls).getD i 0) (idxOps (monoOps (monoIdx l)) (2 ^ j)) 12)

/-- A short relabeling list is admissible for a run: valid transvections with the composite
images of the twelve basis labels. -/
def runOk (ls : List (Fin 2 × Bool)) (S : List IdxOp) : Bool :=
  S.all (fun o => decide (o.Valid 12)) && allTransB S &&
    (List.range 12).all (fun j => Nat.beq (idxOps S (2 ^ j)) ((runImgs ls).getD j 0))

/-- The fused packed action of a run of monomial letters. -/
def tensorRun (w : ℕ) (ls : List (Fin 2 × Bool)) (S : List IdxOp) (X : List SVec) : List SVec :=
  (List.range 24).map (fun i =>
    sflip (allMask w (2 ^ 12)) (runMask w ls) (sops w 12 S (tcol X (runCol ls i))))

/-! ## Index maps -/

theorem idxOps_append (os ps : List IdxOp) (t : ℕ) :
    idxOps (os ++ ps) t = idxOps os (idxOps ps t) := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [List.cons_append, idxOps, ih]

theorem allTransB_append : ∀ (os ps : List IdxOp), allTransB os = true →
    allTransB ps = true → allTransB (os ++ ps) = true
  | [], _, _, h => h
  | .trans _ _ :: os, ps, h1, h2 => allTransB_append os ps h1 h2
  | .flip _ :: _, _, h1, _ => by simp [allTransB] at h1

theorem runOps_valid : ∀ (ls : List (Fin 2 × Bool)), ∀ o ∈ runOps ls, o.Valid 12
  | [] => by simp [runOps]
  | _ :: ls => by
    intro o ho
    simp only [runOps, List.mem_append] at ho
    rcases ho with ho | ho
    · exact runOps_valid ls o ho
    · exact monoOps_valid _ o ho

theorem runOps_allTrans : ∀ (ls : List (Fin 2 × Bool)), allTransB (runOps ls) = true
  | [] => rfl
  | _ :: ls => allTransB_append _ _ (runOps_allTrans ls) (monoOps_allTrans _)

theorem idxOps_lt (os : List IdxOp) (hos : ∀ o ∈ os, o.Valid 12) (t : ℕ) (ht : t < 4096) :
    idxOps os t < 4096 :=
  ((actOps_spec 1 12 os hos 0 (by positivity)).2 t (by simpa using ht)).1

theorem linFold_congr (g g' : ℕ → ℕ) (k : ℕ) : ∀ n, (∀ j < n, g j = g' j) →
    linFold g k n = linFold g' k n
  | 0, _ => rfl
  | n + 1, h => by
    rw [linFold, linFold, linFold_congr g g' k n (fun j hj => h j (by omega)), h n (by omega)]

theorem idxOps_lin (os : List IdxOp) (hos : allTransB os = true) (k : ℕ) (hk : k < 4096) :
    idxOps os k = linFold (fun j => idxOps os (2 ^ j)) k 12 := by
  have e := eq_linFold (idxOps os) (idxOps_xor os hos) k 12
  rwa [Nat.mod_eq_of_lt (by simpa using hk)] at e

theorem runImgs_spec : ∀ (ls : List (Fin 2 × Bool)) (j : ℕ), j < 12 →
    (runImgs ls).getD j 0 = idxOps (runOps ls) (2 ^ j)
  | [], j, hj => by
    simp only [runImgs, runOps, idxOps]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  | l :: ls, j, hj => by
    simp only [runImgs]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    simp only [Option.map_some, Option.getD_some]
    have hA : idxOps (monoOps (monoIdx l)) (2 ^ j) < 4096 :=
      idxOps_lt _ (monoOps_valid _) _ (by
        calc 2 ^ j < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) hj
          _ = 4096 := by norm_num)
    rw [linFold_congr _ (fun i => idxOps (runOps ls) (2 ^ i)) _ 12
      (fun i hi => runImgs_spec ls i hi), ← idxOps_lin _ (runOps_allTrans ls) _ hA,
      runOps, idxOps_append]

theorem runOk_idx (ls : List (Fin 2 × Bool)) (S : List IdxOp) (hok : runOk ls S = true) :
    ∀ k < 4096, idxOps S k = idxOps (runOps ls) k := by
  simp only [runOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Nat.beq_eq,
    List.mem_range] at hok
  obtain ⟨⟨_, ht⟩, hb⟩ := hok
  intro k hk
  rw [idxOps_lin S ht k hk, idxOps_lin _ (runOps_allTrans ls) k hk]
  exact linFold_congr _ _ k 12 (fun j hj => (hb j hj).trans (runImgs_spec ls j hj))

theorem runOk_valid (ls : List (Fin 2 × Bool)) (S : List IdxOp) (hok : runOk ls S = true) :
    ∀ o ∈ S, o.Valid 12 := by
  simp only [runOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  exact hok.1.1

/-! ## Columns and phases -/

set_option maxRecDepth 10000 in
theorem monoCols_lt_fin : ∀ (l : Fin 4) (i : Fin 24), (monoCols l).getD i.val 0 < 24 := by
  decide +kernel

theorem monoCols_lt (l : Fin 4) (i : ℕ) : (monoCols l).getD i 0 < 24 := by
  by_cases hi : i < 24
  · exact monoCols_lt_fin l ⟨i, hi⟩
  · have hlen : (monoCols l).length = 24 := by fin_cases l <;> rfl
    rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem runCol_lt : ∀ (ls : List (Fin 2 × Bool)) (i : ℕ), i < 24 → runCol ls i < 24
  | [], _, h => h
  | _ :: ls, _, _ => runCol_lt ls _ (monoCols_lt _ _)

theorem monoPhaseMask_lt (w : ℕ) (l : Fin 4) : monoPhaseMask w l < 2 ^ (w * 2 ^ 12) := by
  unfold monoPhaseMask
  split_ifs
  · exact qmaskAux_lt w _ 12
  all_goals exact (actOps_spec w 12 _ (monoOps_valid _) _ (qmaskAux_lt w _ 12)).1

theorem runMask_lt (w : ℕ) : ∀ (ls : List (Fin 2 × Bool)), runMask w ls < 2 ^ (w * 2 ^ 12)
  | [] => by simp only [runMask]; positivity
  | l :: ls => Nat.xor_lt_two_pow (monoPhaseMask_lt w _)
      (actOps_spec w 12 _ (monoOps_valid _) _ (runMask_lt w ls)).1

theorem runMask_isFieldMask (w : ℕ) : ∀ (ls : List (Fin 2 × Bool)),
    IsFieldMask w (2 ^ 12) (runMask w ls) (fun k => runPhase ls k = true)
  | [] => (zero_isFieldMask w _).congr (fun t _ => by simp [runPhase])
  | l :: ls => by
    have h1 := monoPhaseMask_isFieldMask w (monoIdx l)
    have h2 := isFieldMask_actOps (monoOps (monoIdx l)) (monoOps_valid _) (runMask_lt w ls)
      (runMask_isFieldMask w ls)
    refine (isFieldMask_xor h1 h2).congr (fun t _ => ?_)
    simp only [runPhase]
    by_cases hp : monoPhaseAt (monoIdx l) t = 1 <;>
      rcases Bool.eq_false_or_eq_true (runPhase ls (idxOps (monoOps (monoIdx l)) t)) with h | h <;>
      simp [hp, h]

/-! ## The sequential and the fused run -/

/-- The sequential action of a run, field by field. -/
theorem tensorWordAll_run {w B : ℕ} (hB : B < 2 ^ w) : ∀ (ls : List (Fin 2 × Bool))
    {X : List SVec}, TBnd w B X →
    TBnd w B (tensorWordAll w (ls.map IdentLetter.mono) X) ∧
    ∀ i < 24, ∀ k < 4096, sval w (tcol (tensorWordAll w (ls.map IdentLetter.mono) X) i) k =
      (if runPhase ls k then -1 else 1) * sval w (tcol X (runCol ls i)) (idxOps (runOps ls) k)
  | [], X, hX => ⟨hX, fun i _ k _ => by simp [tensorWordAll, runPhase, runCol, runOps, idxOps]⟩
  | l :: ls, X, hX => by
    obtain ⟨ih1, ih2⟩ := tensorWordAll_run hB ls hX
    have hY : tensorWordAll w ((l :: ls).map IdentLetter.mono) X =
        tensorMono w (monoIdx l) (tensorWordAll w (ls.map IdentLetter.mono) X) := rfl
    have hcol : ∀ i < 24, tcol (tensorMono w (monoIdx l)
        (tensorWordAll w (ls.map IdentLetter.mono) X)) i = colMono w (monoIdx l)
          (tcol (tensorWordAll w (ls.map IdentLetter.mono) X) ((monoCols (monoIdx l)).getD i 0)) :=
      fun i hi => tcol_range_map _ 24 i hi
    rw [hY]
    refine ⟨fun i hi => ?_, fun i hi k hk => ?_⟩
    · rw [hcol i hi]
      exact (colMono_spec (monoIdx l) (ih1 _ (monoCols_lt _ _)) hB).1
    · rw [hcol i hi, (colMono_spec (monoIdx l) (ih1 _ (monoCols_lt _ _)) hB).2 ⟨k, hk⟩]
      have hA := monoOps_idx (monoIdx l) ⟨k, hk⟩
      simp only at hA
      rw [← hA]
      have hAk : idxOps (monoOps (monoIdx l)) k < 4096 := idxOps_lt _ (monoOps_valid _) k hk
      rw [ih2 _ (monoCols_lt _ _) _ hAk]
      simp only [runPhase, runCol, runOps, idxOps_append]
      by_cases hp : monoPhaseAt (monoIdx l) k = 1 <;>
        rcases Bool.eq_false_or_eq_true (runPhase ls (idxOps (monoOps (monoIdx l)) k)) with
          h | h <;> simp [hp, h]

/-- The fused action of a run, field by field. -/
theorem tensorRun_spec {w B : ℕ} (ls : List (Fin 2 × Bool)) (S : List IdxOp)
    (hok : runOk ls S = true) {X : List SVec} (hX : TBnd w B X) (hB : B < 2 ^ w) :
    TBnd w B (tensorRun w ls S X) ∧
    ∀ i < 24, ∀ k < 4096, sval w (tcol (tensorRun w ls S X) i) k =
      (if runPhase ls k then -1 else 1) * sval w (tcol X (runCol ls i)) (idxOps (runOps ls) k) := by
  have hcol : ∀ i < 24, tcol (tensorRun w ls S X) i = sflip (allMask w (2 ^ 12)) (runMask w ls)
      (sops w 12 S (tcol X (runCol ls i))) := fun i hi => tcol_range_map _ 24 i hi
  have hS := runOk_valid ls S hok
  have key : ∀ i < 24, SBnd w (2 ^ 12) B (tcol (tensorRun w ls S X) i) ∧
      ∀ k < 4096, sval w (tcol (tensorRun w ls S X) i) k =
        (if runPhase ls k then -1 else 1) *
          sval w (tcol X (runCol ls i)) (idxOps (runOps ls) k) := by
    intro i hi
    obtain ⟨s1, s2⟩ := sops_spec S hS (hX _ (runCol_lt ls i hi))
    obtain ⟨f1, f2⟩ := sflip_spec s1 (runMask w ls) _ (runMask_isFieldMask w ls) hB
    rw [hcol i hi]
    refine ⟨f1, fun k hk => ?_⟩
    have hk' : k < 2 ^ 12 := by simpa using hk
    rw [f2 k hk', (s2 k hk').2, runOk_idx ls S hok k hk]
    split_ifs <;> ring
  exact ⟨fun i hi => (key i hi).1, fun i hi => (key i hi).2⟩

/-- The fused run has the rational tensor of the sequential run. -/
theorem tensorRun_rat {w B : ℕ} (ls : List (Fin 2 × Bool)) (S : List IdxOp)
    (hok : runOk ls S = true) {X : List SVec} (hX : TBnd w B X) (hB : B < 2 ^ w) (D : ℚ) :
    tensorRat w (tensorRun w ls S X) D =
      tensorRat w (tensorWordAll w (ls.map IdentLetter.mono) X) D := by
  funext k i
  simp only [tensorRat]
  rw [(tensorRun_spec ls S hok hX hB).2 i.val i.isLt k.val k.isLt,
    (tensorWordAll_run hB ls hX).2 i.val i.isLt k.val k.isLt]

/-! ## Plans of letters and runs -/

/-- A step of a tensor plan: one letter, or a fused run of monomial letters. -/
inductive TPlan
  | letter (l : IdentLetter)
  | run (ls : List (Fin 2 × Bool)) (S : List IdxOp)

/-- The letters of one step. -/
def TPlan.word : TPlan → List IdentLetter
  | .letter l => [l]
  | .run ls _ => ls.map IdentLetter.mono

/-- The packed action of one step. -/
def TPlan.act (w : ℕ) : TPlan → List SVec → List SVec
  | .letter l, X => tensorLetterAll w l X
  | .run ls S, X => tensorRun w ls S X

/-- The admissibility of one step. -/
def TPlan.ok : TPlan → Bool
  | .letter _ => true
  | .run ls S => runOk ls S

/-- The expanded word of a plan. -/
def planWord (ps : List TPlan) : List IdentLetter := ps.flatMap TPlan.word

/-- The packed action of a plan: the last step acts first. -/
def tensorPlan (w : ℕ) : List TPlan → List SVec → List SVec
  | [], X => X
  | p :: ps, X => p.act w (tensorPlan w ps X)

/-- All runs of a plan are admissible. -/
def planOk (ps : List TPlan) : Bool := ps.all TPlan.ok

theorem tensorWordGrowthAll_append (ls ms : List IdentLetter) :
    tensorWordGrowthAll (ls ++ ms) = tensorWordGrowthAll ls * tensorWordGrowthAll ms := by
  induction ls with
  | nil => simp [tensorWordGrowthAll]
  | cons l ls ih => simp only [List.cons_append, tensorWordGrowthAll, ih, Nat.mul_assoc]

theorem tensorWordDenAll_append (ls ms : List IdentLetter) :
    tensorWordDenAll (ls ++ ms) = tensorWordDenAll ls * tensorWordDenAll ms := by
  induction ls with
  | nil => simp [tensorWordDenAll]
  | cons l ls ih => simp only [List.cons_append, tensorWordDenAll, ih, Nat.mul_assoc]

theorem tensorWordGrowthAll_mono (ls : List (Fin 2 × Bool)) :
    tensorWordGrowthAll (ls.map IdentLetter.mono) = 1 := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [tensorWordGrowthAll, ih, letterGrowthAll, letterGrowth]

theorem tensorWordDenAll_mono (ls : List (Fin 2 × Bool)) :
    tensorWordDenAll (ls.map IdentLetter.mono) = 1 := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [tensorWordDenAll, ih, letterDenAll, letterDen]

/-- One step: bounds and the genuine tensor action. -/
theorem TPlan.act_actual {w B : ℕ} (p : TPlan) (hp : p.ok = true) {X : List SVec}
    (hX : TBnd w B X) (hB : tensorWordGrowthAll p.word * B < 2 ^ w) (D : ℚ) :
    TBnd w (tensorWordGrowthAll p.word * B) (p.act w X) ∧
      localTensorRepresentation (identWordFiber p.word)
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (p.act w X) (tensorWordDenAll p.word * D)) := by
  cases p with
  | letter l =>
    have hw := tensorWordAll_actual [l] hX hB D
    simpa [TPlan.word, TPlan.act, tensorWordAll] using hw
  | run ls S =>
    have hok : runOk ls S = true := hp
    have hg := tensorWordGrowthAll_mono ls
    have hd := tensorWordDenAll_mono ls
    simp only [TPlan.word, hg, one_mul] at hB ⊢
    obtain ⟨_, h2⟩ :=
      tensorWordAll_actual (ls.map IdentLetter.mono) hX (by rw [hg, one_mul]; exact hB) D
    refine ⟨(tensorRun_spec ls S hok hX hB).1, ?_⟩
    rw [h2, hd, TPlan.act, tensorRun_rat ls S hok hX hB]

/-- A plan: bounds and the genuine tensor action of the expanded word. -/
theorem tensorPlan_actual {w B : ℕ} : ∀ (ps : List TPlan), planOk ps = true → ∀ {X : List SVec},
    TBnd w B X → tensorWordGrowthAll (planWord ps) * B < 2 ^ w → ∀ (D : ℚ),
    TBnd w (tensorWordGrowthAll (planWord ps) * B) (tensorPlan w ps X) ∧
      localTensorRepresentation (identWordFiber (planWord ps))
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorPlan w ps X) (tensorWordDenAll (planWord ps) * D))
  | [], _, X, hX, _, D => by
    refine ⟨by simpa [planWord, tensorWordGrowthAll, tensorPlan] using hX, ?_⟩
    simp [planWord, identWordFiber, tensorPlan, tensorWordDenAll]
  | p :: ps, hok, X, hX, hB, D => by
    simp only [planOk, List.all_cons, Bool.and_eq_true] at hok
    have hw : planWord (p :: ps) = p.word ++ planWord ps := by simp [planWord]
    rw [hw, tensorWordGrowthAll_append] at hB
    have hpos : 0 < tensorWordGrowthAll p.word := by
      have : ∀ ls : List IdentLetter, 0 < tensorWordGrowthAll ls := by
        intro ls
        induction ls with
        | nil => simp [tensorWordGrowthAll]
        | cons l ls ih =>
          simp only [tensorWordGrowthAll]
          have : 0 < letterGrowthAll l := by cases l <;> simp [letterGrowthAll, letterGrowth]
          positivity
      exact this _
    have hB1 : tensorWordGrowthAll (planWord ps) * B < 2 ^ w := by
      calc tensorWordGrowthAll (planWord ps) * B
          ≤ tensorWordGrowthAll p.word * (tensorWordGrowthAll (planWord ps) * B) :=
            Nat.le_mul_of_pos_left _ hpos
        _ = tensorWordGrowthAll p.word * tensorWordGrowthAll (planWord ps) * B := by ring
        _ < 2 ^ w := hB
    obtain ⟨h1, h2⟩ := tensorPlan_actual ps hok.2 hX hB1 D
    have hB2 : tensorWordGrowthAll p.word * (tensorWordGrowthAll (planWord ps) * B) < 2 ^ w := by
      calc tensorWordGrowthAll p.word * (tensorWordGrowthAll (planWord ps) * B)
          = tensorWordGrowthAll p.word * tensorWordGrowthAll (planWord ps) * B := by ring
        _ < 2 ^ w := hB
    obtain ⟨h3, h4⟩ := TPlan.act_actual p hok.1 h1 hB2 (tensorWordDenAll (planWord ps) * D)
    rw [hw, tensorWordGrowthAll_append, tensorWordDenAll_append]
    refine ⟨by simpa [tensorPlan, Nat.mul_assoc] using h3, ?_⟩
    rw [identWordFiber_append, map_mul, LinearEquiv.mul_apply, h2, h4]
    simp only [tensorPlan, Nat.cast_mul, mul_assoc]

/-- The real tensor map is injective. -/
theorem rationalTensorReal_injective {T T' : GeneratedAxisGlobalRationalTensor}
    (h : generatedAxisGlobalRationalTensorReal T = generatedAxisGlobalRationalTensorReal T') :
    T = T' := by
  funext k i
  have hk := congrFun (congrFun h (golayLabelCoefficients k)) i
  simp only [generatedAxisGlobalRationalTensorReal, generatedAxisGlobalSpinLabel_coeff] at hk
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have := (div_left_inj' hs).mp hk
  exact_mod_cast this

/-- A plan has the rational tensor of `tensorWordAll` on the expanded word. -/
theorem tensorPlan_rat {w B : ℕ} (ps : List TPlan) (hok : planOk ps = true) {X : List SVec}
    (hX : TBnd w B X) (hB : tensorWordGrowthAll (planWord ps) * B < 2 ^ w) (D : ℚ) :
    tensorRat w (tensorPlan w ps X) (tensorWordDenAll (planWord ps) * D) =
      tensorRat w (tensorWordAll w (planWord ps) X) (tensorWordDenAll (planWord ps) * D) := by
  apply rationalTensorReal_injective
  rw [← (tensorPlan_actual ps hok hX hB D).2, ← (tensorWordAll_actual (planWord ps) hX hB D).2]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorXiFastRun

/-! # The packed Xi letter as three plane operators

The 64 grey translations of the Xi letter are linear in the grey label and their signs form a
quadratic form; in a symplectic basis of the grey labels the 64-term sum factors into three
4-term plane operators.  `colXiF` uses 13 single-bit index translations per column instead of
192 (`colXiG`), with the same field values (`colXiF_spec`); `tensorXiF` replaces `tensorXi`
(`tensorXiF_rat`), and `tensorPlanF` evaluates tensor plans with the fast Xi letter
(`tensorPlanF_actual`, `tensorPlanF_rat`). -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators
set_option autoImplicit false

/-! ## Plane operators -/

/-- One plane operator `y ± τ_a y ± τ_b y ± τ_{a ⊕ b} y`, with the translations given by bit
lists. -/
def xiPlane (w : ℕ) (sa sb sab : Bool) (ka kb : List ℕ) (y : SVec) : SVec :=
  sadd (sadd y (scond sa (strs w 12 ka y)))
    (sadd (scond sb (strs w 12 kb y)) (scond sab (strs w 12 kb (strs w 12 ka y))))

/-- The fast grey Gaussian of one packed column: three plane operators. -/
def colXiF (w : ℕ) (x : SVec) : SVec :=
  sneg (xiPlane w false false true [3] [2]
    (xiPlane w true true true [1, 2, 3] [0, 1]
      (xiPlane w false true false [10] [11] (colXiPre w x))))

/-- The fast packed Xi tensor operator on numerators. -/
def tensorXiF (w : ℕ) (X : List SVec) : List SVec :=
  let Gs := X.map (colXiF w)
  (List.range 24).map (fun i =>
    ssum ((List.range 4).map (fun b => scond (xiNeg i b) (tcol Gs (4 * (i / 4) + b)))))

/-- Bounds and values of a plane operator. -/
theorem xiPlane_spec {w B : ℕ} (sa sb sab : Bool) (ka kb : List ℕ) (a b : ℕ)
    (hka : ∀ k ∈ ka, k < 12) (hkb : ∀ k ∈ kb, k < 12) (ha : xorBits ka = a)
    (hb : xorBits kb = b) {y : SVec} (hy : SBnd w (2 ^ 12) B y) (hB : 4 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (4 * B) (xiPlane w sa sb sab ka kb y) ∧
      ∀ t < 2 ^ 12, sval w (xiPlane w sa sb sab ka kb y) t =
        sval w y t + (if sa then -1 else 1) * sval w y (t ^^^ a) +
          ((if sb then -1 else 1) * sval w y (t ^^^ b) +
            (if sab then -1 else 1) * sval w y ((t ^^^ b) ^^^ a)) := by
  obtain ⟨ta1, ta2⟩ := strs_spec ka hy hka
  obtain ⟨tb1, tb2⟩ := strs_spec kb hy hkb
  obtain ⟨tab1, tab2⟩ := strs_spec kb ta1 hkb
  obtain ⟨ca1, ca2⟩ := scond_spec sa ta1
  obtain ⟨cb1, cb2⟩ := scond_spec sb tb1
  obtain ⟨cab1, cab2⟩ := scond_spec sab tab1
  have h2 : B + B < 2 ^ w := by omega
  obtain ⟨s1, s1v⟩ := sadd_spec hy ca1 h2
  obtain ⟨s2, s2v⟩ := sadd_spec cb1 cab1 h2
  obtain ⟨s3, s3v⟩ := sadd_spec s1 s2 (by omega)
  refine ⟨(s3.mono (by omega) : SBnd w (2 ^ 12) (4 * B) _), fun t ht => ?_⟩
  unfold xiPlane
  rw [s3v t ht, s1v t ht, s2v t ht, ca2, cb2, cab2, ta2 t ht, tb2 t ht, tab2 t ht,
    ta2 _ (Nat.xor_lt_two_pow ht (xorBits_lt 12 kb hkb)), ha, hb]

/-- A plane operator on functions. -/
def xiPl (sa sb sab : Bool) (a b : ℕ) (g : ℕ → ℤ) (t : ℕ) : ℤ :=
  g t + (if sa then -1 else 1) * g (t ^^^ a) +
    ((if sb then -1 else 1) * g (t ^^^ b) + (if sab then -1 else 1) * g ((t ^^^ b) ^^^ a))

theorem xiPl_congr (sa sb sab : Bool) (a b : ℕ) (ha : a < 4096) (hb : b < 4096)
    (g g' : ℕ → ℤ) (h : ∀ t < 4096, g t = g' t) :
    ∀ t < 4096, xiPl sa sb sab a b g t = xiPl sa sb sab a b g' t := by
  intro t ht
  have h1 : t ^^^ a < 4096 := Nat.xor_lt_two_pow (n := 12) ht ha
  have h2 : t ^^^ b < 4096 := Nat.xor_lt_two_pow (n := 12) ht hb
  have h3 : (t ^^^ b) ^^^ a < 4096 := Nat.xor_lt_two_pow (n := 12) h2 ha
  simp only [xiPl, h t ht, h _ h1, h _ h2, h _ h3]

/-- The grey Gaussian of a column in terms of its Gamma-signed column. -/
theorem colXiG_val {w B : ℕ} {x : SVec} (hx : SBnd w (2 ^ 12) B x) (hB : 64 * B < 2 ^ w)
    (k : ℕ) (hk : k < 4096) :
    sval w (colXiG w x) k = ∑ n ∈ Finset.range 64,
      (if xiQBits.testBit n then 1 else -1) * sval w (colXiPre w x) (k ^^^ xiCodeTab.getD n 0) := by
  have hB1 : B < 2 ^ w := by omega
  obtain ⟨p1, _⟩ := colXiPre_spec hx hB1
  have hterm : ∀ y ∈ (List.range 64).map (fun n =>
      scond (!xiQBits.testBit n) (strs w 12 (bitsOf (xiCodeTab.getD n 0)) (colXiPre w x))),
      SBnd w (2 ^ 12) B y := by
    intro y hy
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hy
    exact (scond_spec _ (strs_spec _ p1 (bitsOf_lt _)).1).1
  obtain ⟨_, s2⟩ := ssum_spec _ hterm (by simpa using hB)
  unfold colXiG
  rw [s2 k (by simpa using hk), List.map_map, list_sum_map_range]
  apply Finset.sum_congr rfl
  intro n hn
  have hc := xiCodeTab_lt n (Finset.mem_range.mp hn)
  simp only [Function.comp_apply]
  rw [(scond_spec _ (strs_spec _ p1 (bitsOf_lt _)).1).2,
    (strs_spec _ p1 (bitsOf_lt _)).2 k (by simpa using hk), xorBits_bitsOf _ hc]
  cases xiQBits.testBit n <;> simp

/-- Bounds and values of the fast grey Gaussian: the values of `colXiG`. -/
theorem colXiF_spec {w B : ℕ} {x : SVec} (hx : SBnd w (2 ^ 12) B x) (hB : 64 * B < 2 ^ w) :
    SBnd w (2 ^ 12) (64 * B) (colXiF w x) ∧
      ∀ k < 4096, sval w (colXiF w x) k = sval w (colXiG w x) k := by
  have hB1 : B < 2 ^ w := by omega
  obtain ⟨p1, _⟩ := colXiPre_spec hx hB1
  obtain ⟨q1, q1v⟩ := xiPlane_spec false true false [10] [11] 1024 2048 (by decide) (by decide)
    (by decide) (by decide) p1 (by omega)
  obtain ⟨q2, q2v⟩ := xiPlane_spec true true true [1, 2, 3] [0, 1] 14 3 (by decide) (by decide)
    (by decide) (by decide) q1 (by omega)
  obtain ⟨q3, q3v⟩ := xiPlane_spec false false true [3] [2] 8 4 (by decide) (by decide)
    (by decide) (by decide) q2 (by omega)
  obtain ⟨n3, n3v⟩ := sneg_spec q3
  refine ⟨(n3.mono (by omega) : SBnd w (2 ^ 12) (64 * B) _), fun k hk => ?_⟩
  set y := colXiPre w x with hy
  set y1 := xiPlane w false true false [10] [11] y
  set y2 := xiPlane w true true true [1, 2, 3] [0, 1] y1
  have h1 : ∀ t < 4096, sval w y1 t = xiPl false true false 1024 2048 (sval w y) t :=
    fun t ht => q1v t (by simpa using ht)
  have h2 : ∀ t < 4096, sval w y2 t =
      xiPl true true true 14 3 (xiPl false true false 1024 2048 (sval w y)) t := by
    intro t ht
    rw [q2v t (by simpa using ht)]
    exact xiPl_congr true true true 14 3 (by norm_num) (by norm_num) _ _ h1 t ht
  have h3 : sval w (colXiF w x) k = -(xiPl false false true 8 4
      (xiPl true true true 14 3 (xiPl false true false 1024 2048 (sval w y))) k) := by
    unfold colXiF
    rw [n3v, q3v k (by simpa using hk)]
    congr 1
    exact xiPl_congr false false true 8 4 (by norm_num) (by norm_num) _ _ h2 k hk
  rw [h3, colXiG_val hx hB k hk, ← hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp (config := { decide := true }) only [xiCodeTab, xiPl, List.getD_cons_succ,
    List.getD_cons_zero, Nat.xor_assoc, Nat.reduceXor, Nat.xor_zero, ↓reduceIte]
  ring

/-- A plane operator fixes zero. -/
theorem xiPlane_zero (w : ℕ) (sa sb sab : Bool) (ka kb : List ℕ) :
    xiPlane w sa sb sab ka kb szero = szero := by
  simp only [xiPlane, strs_zero, scond_zero]
  rfl

/-- The fast grey Gaussian fixes zero. -/
theorem colXiF_zero (w : ℕ) : colXiF w szero = szero := by
  simp only [colXiF, colXiPre_zero, xiPlane_zero]
  rfl

/-- The spatial mixing of the Xi letter over any column map: bounds and values. -/
theorem xiMix_spec (f : SVec → SVec) (hf0 : f szero = szero) {w B C : ℕ} {X : List SVec}
    (hX : TBnd w B X) (hfb : ∀ x, SBnd w (2 ^ 12) B x → SBnd w (2 ^ 12) C (f x))
    (hC : 4 * C < 2 ^ w) (i : ℕ) (hi : i < 24) :
    SBnd w (2 ^ 12) (4 * C) (ssum ((List.range 4).map (fun b =>
        scond (xiNeg i b) (tcol (X.map f) (4 * (i / 4) + b))))) ∧
      ∀ k < 4096, sval w (ssum ((List.range 4).map (fun b =>
        scond (xiNeg i b) (tcol (X.map f) (4 * (i / 4) + b))))) k =
        ∑ b ∈ Finset.range 4, (if xiNeg i b then -1 else 1) *
          sval w (f (tcol X (4 * (i / 4) + b))) k := by
  have hidx : ∀ b < 4, 4 * (i / 4) + b < 24 := by intro b hb; omega
  have hterm : ∀ y ∈ (List.range 4).map (fun b =>
      scond (xiNeg i b) (tcol (X.map f) (4 * (i / 4) + b))), SBnd w (2 ^ 12) C y := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    rw [tcol_map _ hf0]
    exact (scond_spec _ (hfb _ (hX _ (hidx b (List.mem_range.mp hb))))).1
  obtain ⟨s1, s2⟩ := ssum_spec _ hterm (by simpa using hC)
  refine ⟨(s1.mono (by simp) : SBnd w (2 ^ 12) (4 * C) _), fun k hk => ?_⟩
  rw [s2 k (by simpa using hk), List.map_map, list_sum_map_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Function.comp_apply]
  rw [tcol_map _ hf0]
  exact (scond_spec _ (hfb _ (hX _ (hidx b (Finset.mem_range.mp hb))))).2 k

/-- The fast Xi letter has the bounds and the rational tensor of the Xi letter. -/
theorem tensorXiF_rat {w B : ℕ} {X : List SVec} (hX : TBnd w B X) (hB : 4 * (64 * B) < 2 ^ w)
    (D : ℚ) : TBnd w (4 * (64 * B)) (tensorXiF w X) ∧
      tensorRat w (tensorXiF w X) D = tensorRat w (tensorXi w X) D := by
  have hB64 : 64 * B < 2 ^ w := by omega
  have hF := xiMix_spec (colXiF w) (colXiF_zero w) hX (fun x hx => (colXiF_spec hx hB64).1) hB
  have hG := xiMix_spec (colXiG w) (colXiG_zero w) hX (fun x hx => (colXiG_spec hx hB64).1) hB
  have hcF : ∀ i < 24, tcol (tensorXiF w X) i = ssum ((List.range 4).map (fun b =>
      scond (xiNeg i b) (tcol (X.map (colXiF w)) (4 * (i / 4) + b)))) := by
    intro i hi
    unfold tensorXiF
    exact tcol_range_map _ 24 i hi
  have hcG : ∀ i < 24, tcol (tensorXi w X) i = ssum ((List.range 4).map (fun b =>
      scond (xiNeg i b) (tcol (X.map (colXiG w)) (4 * (i / 4) + b)))) := by
    intro i hi
    unfold tensorXi
    exact tcol_range_map _ 24 i hi
  refine ⟨fun i hi => by rw [hcF i hi]; exact (hF i hi).1, ?_⟩
  funext k i
  have hsum : ∑ b ∈ Finset.range 4, (if xiNeg i.val b then -1 else 1) *
      sval w (colXiF w (tcol X (4 * (i.val / 4) + b))) k.val =
      ∑ b ∈ Finset.range 4, (if xiNeg i.val b then -1 else 1) *
        sval w (colXiG w (tcol X (4 * (i.val / 4) + b))) k.val := by
    apply Finset.sum_congr rfl
    intro b hb
    have hcolb : 4 * (i.val / 4) + b < 24 := by
      have := Finset.mem_range.mp hb
      omega
    rw [(colXiF_spec (hX _ hcolb) hB64).2 k.val k.isLt]
  have e1 := (hF i.val i.isLt).2 k.val k.isLt
  have e2 := (hG i.val i.isLt).2 k.val k.isLt
  rw [← hcF i.val i.isLt] at e1
  rw [← hcG i.val i.isLt] at e2
  simp only [tensorRat]
  rw [e1, e2, hsum]


/-! ## A fast phase mask for runs -/

/-- Short relabeling lists of the four monomial letters (same index maps as `monoOps`). -/
def monoOpsS : Fin 4 → List IdxOp := ![
  [.trans 0 11, .trans 0 10, .trans 8 3, .trans 7 0, .trans 0 1, .trans 7 6, .trans 5 0,
    .trans 9 11, .trans 10 1, .trans 8 2, .trans 9 2, .trans 10 4, .trans 0 8, .trans 4 3,
    .trans 4 5, .trans 10 6, .trans 6 2, .trans 5 2, .trans 2 9, .trans 9 8, .trans 1 8,
    .trans 6 7, .trans 7 3, .trans 8 3, .trans 3 9, .trans 9 11, .trans 9 2, .trans 8 11],
  [.trans 8 11, .trans 9 2, .trans 9 11, .trans 3 9, .trans 8 3, .trans 7 3, .trans 6 7,
    .trans 1 8, .trans 9 8, .trans 2 9, .trans 5 2, .trans 6 2, .trans 10 6, .trans 4 5,
    .trans 4 3, .trans 0 8, .trans 10 4, .trans 9 2, .trans 8 2, .trans 10 1, .trans 9 11,
    .trans 5 0, .trans 7 6, .trans 0 1, .trans 7 0, .trans 8 3, .trans 0 10, .trans 0 11],
  [.trans 3 2, .trans 9 7, .trans 9 5, .trans 9 3, .trans 2 10, .trans 8 6, .trans 1 5,
    .trans 8 1, .trans 1 4, .trans 1 8, .trans 5 6, .trans 8 1, .trans 1 9, .trans 8 0,
    .trans 0 3, .trans 9 0, .trans 0 9, .trans 6 5, .trans 5 6, .trans 9 7, .trans 9 5,
    .trans 9 0, .trans 3 2],
  [.trans 3 2, .trans 9 7, .trans 9 5, .trans 9 3, .trans 2 10, .trans 8 6, .trans 1 5,
    .trans 8 1, .trans 1 4, .trans 1 8, .trans 5 6, .trans 8 1, .trans 1 9, .trans 8 0,
    .trans 0 3, .trans 9 0, .trans 0 9, .trans 6 5, .trans 5 6, .trans 9 7, .trans 9 5,
    .trans 9 0, .trans 3 2]]

theorem monoOpsS_valid : ∀ l : Fin 4, ∀ o ∈ monoOpsS l, o.Valid 12 := by
  decide +kernel

theorem monoOpsS_allTrans : ∀ l : Fin 4, allTransB (monoOpsS l) = true := by
  decide +kernel

theorem monoOpsS_basis : ∀ (l : Fin 4) (j : Fin 12),
    idxOps (monoOpsS l) (2 ^ j.val) = idxOps (monoOps l) (2 ^ j.val) := by
  decide +kernel

theorem monoOpsS_idx (l : Fin 4) (k : ℕ) (hk : k < 4096) :
    idxOps (monoOpsS l) k = idxOps (monoOps l) k := by
  rw [idxOps_lin _ (monoOpsS_allTrans l) k hk, idxOps_lin _ (monoOps_allTrans l) k hk]
  exact linFold_congr _ _ k 12 (fun j hj => monoOpsS_basis l ⟨j, hj⟩)

/-- The phase mask of a run, folded with the short letter lists. -/
def runMaskF (w : ℕ) : List (Fin 2 × Bool) → ℕ
  | [] => 0
  | l :: ls => monoPhaseMask w (monoIdx l) ^^^ actOps w 12 (monoOpsS (monoIdx l)) (runMaskF w ls)

theorem runMaskF_lt (w : ℕ) : ∀ (ls : List (Fin 2 × Bool)), runMaskF w ls < 2 ^ (w * 2 ^ 12)
  | [] => by simp only [runMaskF]; positivity
  | l :: ls => Nat.xor_lt_two_pow (monoPhaseMask_lt w _)
      (actOps_spec w 12 _ (monoOpsS_valid _) _ (runMaskF_lt w ls)).1

theorem runMaskF_isFieldMask (w : ℕ) : ∀ (ls : List (Fin 2 × Bool)),
    IsFieldMask w (2 ^ 12) (runMaskF w ls) (fun k => runPhase ls k = true)
  | [] => (zero_isFieldMask w _).congr (fun t _ => by simp [runPhase])
  | l :: ls => by
    have h1 := monoPhaseMask_isFieldMask w (monoIdx l)
    have h2 := isFieldMask_actOps (monoOpsS (monoIdx l)) (monoOpsS_valid _) (runMaskF_lt w ls)
      (runMaskF_isFieldMask w ls)
    refine (isFieldMask_xor h1 h2).congr (fun t ht => ?_)
    have ht' : t < 4096 := by simpa using ht
    simp only [runPhase, monoOpsS_idx _ t ht']
    by_cases hp : monoPhaseAt (monoIdx l) t = 1 <;>
      rcases Bool.eq_false_or_eq_true (runPhase ls (idxOps (monoOps (monoIdx l)) t)) with
        h | h <;> simp [hp, h]

/-- Packed numbers below `2^(w n)` with the same fields are equal. -/
theorem eq_of_fld_eq (w n P Q : ℕ) (hP : P < 2 ^ (w * n)) (hQ : Q < 2 ^ (w * n))
    (h : ∀ i < n, fld w P i = fld w Q i) : P = Q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hw : w = 0
  · subst hw
    rw [Nat.zero_mul, pow_zero] at hP hQ
    have hP0 : P = 0 := by omega
    have hQ0 : Q = 0 := by omega
    rw [hP0, hQ0]
  have hw' : 0 < w := Nat.pos_of_ne_zero hw
  by_cases hb : b < w * n
  · have hi : b / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw']
      linarith [Nat.mul_comm w n]
    have hr : b % w < w := Nat.mod_lt _ hw'
    have e := congrArg (fun x => Nat.testBit x (b % w)) (h (b / w) hi)
    simp only [testBit_fld, hr, decide_true, Bool.true_and] at e
    have hb' : w * (b / w) + b % w = b := Nat.div_add_mod b w
    rwa [hb'] at e
  · have h1 : P.testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have h2 : Q.testBit b = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hQ (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, h2]

/-- The fast phase mask is the phase mask. -/
theorem runMaskF_eq (w : ℕ) (ls : List (Fin 2 × Bool)) : runMaskF w ls = runMask w ls := by
  apply eq_of_fld_eq w (2 ^ 12) _ _ (runMaskF_lt w ls) (runMask_lt w ls)
  intro i hi
  rw [runMaskF_isFieldMask w ls i hi, runMask_isFieldMask w ls i hi]

/-- The fused run with the fast phase mask. -/
def tensorRunF (w : ℕ) (ls : List (Fin 2 × Bool)) (S : List IdxOp) (X : List SVec) :
    List SVec :=
  (List.range 24).map (fun i =>
    sflip (allMask w (2 ^ 12)) (runMaskF w ls) (sops w 12 S (tcol X (runCol ls i))))

/-- The fused run with the fast phase mask is the fused run. -/
theorem tensorRunF_eq (w : ℕ) (ls : List (Fin 2 × Bool)) (S : List IdxOp) (X : List SVec) :
    tensorRunF w ls S X = tensorRun w ls S X := by
  simp only [tensorRunF, tensorRun, runMaskF_eq]

/-! ## Plans with the fast Xi letter -/

/-- The packed action of one plan step with the fast Xi letter. -/
def TPlan.actF (w : ℕ) : TPlan → List SVec → List SVec
  | .letter .xi, X => tensorXiF w X
  | .letter l, X => tensorLetterAll w l X
  | .run ls S, X => tensorRunF w ls S X

/-- The packed action of a plan with the fast Xi letter: the last step acts first. -/
def tensorPlanF (w : ℕ) : List TPlan → List SVec → List SVec
  | [], X => X
  | p :: ps, X => p.actF w (tensorPlanF w ps X)

/-- One fast step has the bounds and the rational tensor of the step. -/
theorem TPlan.actF_rat {w B : ℕ} (p : TPlan) {X : List SVec} (hX : TBnd w B X)
    (hB : tensorWordGrowthAll p.word * B < 2 ^ w) (hp : p.ok = true) (D : ℚ) :
    TBnd w (tensorWordGrowthAll p.word * B) (p.actF w X) ∧
      tensorRat w (p.actF w X) D = tensorRat w (p.act w X) D := by
  cases p with
  | letter l =>
    cases l with
    | xi =>
      have hg : tensorWordGrowthAll (TPlan.letter .xi).word * B = 4 * (64 * B) := by
        simp only [TPlan.word, tensorWordGrowthAll, letterGrowthAll, letterGrowth]
        ring
      rw [hg] at hB ⊢
      obtain ⟨h1, h2⟩ := tensorXiF_rat hX hB D
      exact ⟨h1, h2⟩
    | sign a ε =>
      exact ⟨(TPlan.act_actual (.letter (.sign a ε)) hp hX hB 1).1, rfl⟩
    | mono m =>
      exact ⟨(TPlan.act_actual (.letter (.mono m)) hp hX hB 1).1, rfl⟩
    | qel g =>
      exact ⟨(TPlan.act_actual (.letter (.qel g)) hp hX hB 1).1, rfl⟩
  | run ls S =>
    have he : (TPlan.run ls S).actF w X = (TPlan.run ls S).act w X := tensorRunF_eq w ls S X
    rw [he]
    exact ⟨(TPlan.act_actual (.run ls S) hp hX hB 1).1, rfl⟩

/-- A plan with the fast Xi letter: bounds and the genuine tensor action of the expanded word. -/
theorem tensorPlanF_actual {w B : ℕ} : ∀ (ps : List TPlan), planOk ps = true →
    ∀ {X : List SVec}, TBnd w B X → tensorWordGrowthAll (planWord ps) * B < 2 ^ w → ∀ (D : ℚ),
    TBnd w (tensorWordGrowthAll (planWord ps) * B) (tensorPlanF w ps X) ∧
      localTensorRepresentation (identWordFiber (planWord ps))
        (generatedAxisGlobalRationalTensorReal (tensorRat w X D)) =
      generatedAxisGlobalRationalTensorReal
        (tensorRat w (tensorPlanF w ps X) (tensorWordDenAll (planWord ps) * D))
  | [], _, X, hX, _, D => by
    refine ⟨by simpa [planWord, tensorWordGrowthAll, tensorPlanF] using hX, ?_⟩
    simp [planWord, identWordFiber, tensorPlanF, tensorWordDenAll]
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
    obtain ⟨h1, h2⟩ := tensorPlanF_actual ps hok.2 hX hB1 D
    have hB2 : tensorWordGrowthAll p.word * (tensorWordGrowthAll (planWord ps) * B) < 2 ^ w := by
      calc tensorWordGrowthAll p.word * (tensorWordGrowthAll (planWord ps) * B)
          = tensorWordGrowthAll p.word * tensorWordGrowthAll (planWord ps) * B := by ring
        _ < 2 ^ w := hB
    obtain ⟨_, h4⟩ := TPlan.act_actual p hok.1 h1 hB2 (tensorWordDenAll (planWord ps) * D)
    obtain ⟨f1, f2⟩ := TPlan.actF_rat p h1 hB2 hok.1
      (tensorWordDenAll p.word * (tensorWordDenAll (planWord ps) * D))
    rw [hw, tensorWordGrowthAll_append, tensorWordDenAll_append]
    refine ⟨by simpa [tensorPlanF, Nat.mul_assoc] using f1, ?_⟩
    rw [identWordFiber_append, map_mul, LinearEquiv.mul_apply, h2, h4]
    simp only [tensorPlanF, Nat.cast_mul, mul_assoc, f2]

/-- A plan with the fast Xi letter has the rational tensor of `tensorWordAll`. -/
theorem tensorPlanF_rat {w B : ℕ} (ps : List TPlan) (hok : planOk ps = true) {X : List SVec}
    (hX : TBnd w B X) (hB : tensorWordGrowthAll (planWord ps) * B < 2 ^ w) (D : ℚ) :
    tensorRat w (tensorPlanF w ps X) (tensorWordDenAll (planWord ps) * D) =
      tensorRat w (tensorWordAll w (planWord ps) X) (tensorWordDenAll (planWord ps) * D) := by
  apply rationalTensorReal_injective
  rw [← (tensorPlanF_actual ps hok hX hB D).2, ← (tensorWordAll_actual (planWord ps) hX hB D).2]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

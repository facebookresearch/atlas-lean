/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.DeriveFintype
public import MathlibExt.Computability.TuringMachine.Program

/-!
# Cook-Levin: the counter-machine view shared by the clause generators

Every clause generator is a `TM2` machine with one Bool output stack and unit counters indexed by
a finite type `C`. `SK C`/`SΓ C` are its stacks and alphabets, `st f o` the stacks holding counter
values `f` and output `o`. The run lemmas restate the program-library primitives of
`MetaMathlibExt.TM2Program` in this view: emission (`emitS`, `emitOut`, `emitR_st`), increment
(`incS`), draining and transfers (`drainS`, `xferES`, `copyS`, `addU_st_single`, `addU_st_pair`),
multiplication (`mulS`, `mulS_run`, with stages `MS`), gap emission (`gapS`), and the loop
`stLoop`.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.CounterView

open MetaMathlibExt MetaMathlibExt.TM2Program Turing Function

/-- Stages of a `mul_run` site. -/
inductive MS | head | body | l2 | rest
  deriving DecidableEq
instance MS.instFintypeEnumFix : Fintype MS where
  elems := ⟨↑[MS.head, MS.body, MS.l2, MS.rest], by decide⟩
  complete := fun x => by cases x <;> decide


/-- Stacks of a counter machine: a Bool output and unit counters indexed by `C`. -/
inductive SK (C : Type)
  | out
  | c (x : C)
  deriving DecidableEq, Fintype

/-- Alphabets of a counter machine: Bool output, unit counters. -/
abbrev SΓ (C : Type) : SK C → Type
  | .out => Bool
  | .c _ => Unit

section View

variable {C : Type} [DecidableEq C]

/-- Stacks from counter values `f` and output `o`. -/
def st (f : C → ℕ) (o : List Bool) : ∀ k, List (SΓ C k)
  | .out => o
  | .c x => cnt () (f x)

omit [DecidableEq C] in
@[simp] theorem st_c (f : C → ℕ) (o : List Bool) (x : C) : st f o (.c x) = cnt () (f x) := rfl
omit [DecidableEq C] in
@[simp] theorem st_out (f : C → ℕ) (o : List Bool) : st f o .out = o := rfl

theorem update_st_c (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (cnt () n) = st (update f x n) o := by
  funext k
  rcases k with _ | y
  · rfl
  · by_cases h : y = x
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; simp [update_of_ne h]

theorem update_st_nil (f : C → ℕ) (o : List Bool) (x : C) :
    update (st f o) (.c x) [] = st (update f x 0) o := update_st_c f o x 0

theorem update_st_out (f : C → ℕ) (o l : List Bool) : update (st f o) .out l = st f l := by
  funext k
  rcases k with _ | y
  · simp
  · rw [update_of_ne (by simp)]; rfl

theorem addU_nil {K : Type} [DecidableEq K] {Γ : K → Type} (n : ℕ) (S : ∀ k, List (Γ k)) :
    addU [] n S = S := rfl

variable {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem emitS {self next : Λ} {x : C} {n : ℕ}
    (hp : M self = emitR (.c x) (List.replicate n ()) next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (n + F x)) o⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c] at this
  exact this

theorem emitOut {self next : Λ} {ys : List Bool} (hp : M self = emitR .out ys next)
    (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st F (ys ++ o)⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_out, update_st_out] at this
  exact this

theorem incS {self next : Λ} {x : C} (hp : M self = incr (.c x) () next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (F x + 1)) o⟩ := by
  have := incr_run_cnt hp v (S := st F o) (n := F x) rfl
  rw [update_st_c] at this
  exact this

theorem drainS {self next : Λ} {x : C} (hp : M self = xfer (.c x) [] self next) (F : C → ℕ)
    (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (update F x 0) o⟩ := by
  have := xfer_run hp (by simp [List.NodupKeys]) (by simp) () (F x) v (st F o) rfl
  rw [addU_nil, update_st_nil] at this
  exact this

theorem xferES {self next : Λ} {x : C} {ys : List Bool}
    (hp : M self = xferE (.c x) .out ys self next) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩
      ⟨some next, false, st (update F x 0) (rep ys (F x) ++ o)⟩ := by
  have := xferE_run hp (by simp) () (F x) v (st F o) rfl
  rw [update_st_nil, update_st_out, st_out] at this
  exact this

theorem copyS {l₁ l₂ next : Λ} {a c t : C}
    (h₁ : M l₁ = xfer (.c a) [⟨.c c, ()⟩, ⟨.c t, ()⟩] l₁ l₂)
    (h₂ : M l₂ = xfer (.c t) [⟨.c a, ()⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (F : C → ℕ) (ht : F t = 0) (v : Bool)
    (o : List Bool) :
    Run M (2 * F a + 2) ⟨some l₁, v, st F o⟩
      ⟨some next, false, st (update F c (F a + F c)) o⟩ := by
  have := copy_run h₁ h₂ (by simpa using hac) (by simpa using hat) (by simpa using hct) (F a)
    (F c) v (st F o) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

/-- A `mul_run` site `c += a · b` (index stack `ad`, scratch `t`), for any counter machine. -/
def mulS (a ad b c t : C) (mk : MS → Λ) (next : Λ) : MS → TM2.Stmt (SΓ C) Λ Bool
  | .head => forHead (.c a) (.c ad) () (mk .body) (mk .rest)
  | .body => xfer (.c b) [⟨.c c, ()⟩, ⟨.c t, ()⟩] (mk .body) (mk .l2)
  | .l2 => xfer (.c t) [⟨.c b, ()⟩] (mk .l2) (mk .head)
  | .rest => xfer (.c ad) [⟨.c a, ()⟩] (mk .rest) next

theorem mulS_run {a ad b c t : C} {mk : MS → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = mulS a ad b c t mk next s)
    (hnd : ([.c a, .c ad, .c b, .c c, .c t] : List (SK C)).Nodup)
    (F : C → ℕ) (had : F ad = 0) (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (F a * (2 * F b + 3) + F a + 2) ⟨some (mk .head), v, st F o⟩
      ⟨some next, false, st (update F c (F a * F b + F c)) o⟩ := by
  have := mul_run (hp .head) (hp .body) (hp .l2) (hp .rest) hnd (F a) (F b) (F c) v (st F o) rfl
    (by simp [had]) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

/-- Gap emission (`emitDiff_run`) in the counter view. -/
theorem gapS {P Q T1 T2 : C} {ys : List Bool} {dec cmpL emitL ifZero next : Λ}
    {r rB out : Ordering → Λ}
    (hdec : M dec = decr (.c P) ifZero cmpL)
    (hcmp : M cmpL = cmpStep (.c P) (.c Q) (.c T1) (.c T2) () () cmpL (r .lt) (r .eq) (r .gt))
    (hr : ∀ o, M (r o) = xfer (.c T1) [⟨.c P, ()⟩] (r o) (rB o))
    (hrB : ∀ o, M (rB o) = xfer (.c T2) [⟨.c Q, ()⟩] (rB o) (out o))
    (hout : ∀ o, out o = if o = .eq then next else emitL)
    (hemit : M emitL = emitR .out ys dec)
    (hnd : ([.c P, .c Q, .c T1, .c T2, .out] : List (SK C)).Nodup) (q gap : ℕ) (F : C → ℕ)
    (hP : F P = q + gap + 1) (hQ : F Q = q) (h1 : F T1 = 0) (h2 : F T2 = 0) (v : Bool)
    (o : List Bool) :
    Run M (gap * (3 * q + 6) + 3 * q + 4) ⟨some dec, v, st F o⟩
      ⟨some next, false, st (update F P q) (rep ys gap ++ o)⟩ := by
  have := emitDiff_run hdec hcmp hr hrB hout hemit hnd q gap v (st F o) (by simp [hP])
    (by simp [hQ]) (by simp [h1]) (by simp [h2])
  rw [update_st_c, update_st_out, st_out] at this
  exact this

/-- Transport a budgeted run along an equality of counter functions. -/
theorem bud_st {K X : ℕ} {F F' : C → ℕ} {l : Option Λ} {v : Bool} {o : List Bool}
    {d : TM2.Cfg (SΓ C) Λ Bool} (h : F = F') (h' : Bud M K X ⟨l, v, st F' o⟩ d) :
    Bud M K X ⟨l, v, st F o⟩ d := h ▸ h'

omit [DecidableEq C] in
theorem st_eta (S : ∀ k, List (SΓ C k)) : S = st (fun x => (S (.c x)).length) (S .out) := by
  funext k
  rcases k with _ | x
  · rfl
  · exact List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

/-- **A runtime `for` loop in the counter view.** The body runs with the loop counter `c` holding
the index value `t` (descending, `n-1, …, 0`) and must restore every counter; it prepends
`blk t`. The loop prepends the blocks in ascending order. -/
theorem stLoop {c cd : C} {head body rest next : Λ}
    (hHead : M head = forHead (.c c) (.c cd) () body rest)
    (hRest : M rest = xfer (.c cd) [⟨.c c, ()⟩] rest next) (hc : c ≠ cd) (n B : ℕ)
    (blk : ℕ → List Bool) (f : C → ℕ) (hfc : f c = n) (hfcd : f cd = 0)
    (hbody : ∀ t < n, ∀ o, ∃ v', RunLe M B
      ⟨some body, true, st (update (update f c t) cd (n - t)) o⟩
      ⟨some head, v', st (update (update f c t) cd (n - t)) (blk t ++ o)⟩)
    (v : Bool) (o : List Bool) :
    RunLe M (n * (B + 1) + n + 2) ⟨some head, v, st f o⟩
      ⟨some next, false, st f ((List.range n).flatMap blk ++ o)⟩ := by
  obtain ⟨S', hrun, h'c, h'cd, h'o, h'x⟩ := forLoop_le (M := M) (c := .c c) (cd := .c cd)
    (uc := ()) (ucd := ()) hHead
    hRest (by simpa using hc) n B
    (fun i S => S .out = (List.range' (n - i) i).flatMap blk ++ o ∧
      ∀ x, x ≠ c → x ≠ cd → (S (.c x)).length = f x)
    (fun i S S' h ⟨h1, h2⟩ => ⟨by rw [h .out (by simp) (by simp), h1],
      fun x hx1 hx2 => by rw [h (.c x) (by simpa using hx1) (by simpa using hx2), h2 x hx1 hx2]⟩)
    (fun i hi S hS1 hS2 ⟨h1, h2⟩ => by
      have hS : S = st (update (update f c (n - 1 - i)) cd (n - (n - 1 - i))) (S .out) := by
        funext k
        rcases k with _ | x
        · rfl
        · by_cases hx1 : x = c
          · subst hx1; rw [hS1]; simp [hc]
          · by_cases hx2 : x = cd
            · subst hx2; rw [hS2]; simp only [st_c, update_self]; congr 1; omega
            · simp only [st_c, update_of_ne hx2, update_of_ne hx1]
              exact List.eq_replicate_iff.2 ⟨h2 x hx1 hx2, fun _ _ => rfl⟩
      obtain ⟨v', r⟩ := hbody (n - 1 - i) (by omega) (S .out)
      rw [← hS] at r
      refine ⟨v', _, r, ?_, ?_, ?_, fun x hx1 hx2 => ?_⟩
      · rw [hS1]; simp [hc]
      · rw [hS2]; simp only [st_c, update_self]; congr 1; omega
      · simp only [st_out, h1]
        rw [show n - (i + 1) = n - 1 - i by omega, List.range'_succ,
          show n - 1 - i + 1 = n - i by omega, List.flatMap_cons, List.append_assoc]
      · simp [update_of_ne hx1, update_of_ne hx2])
    v (st f o) (by simp [hfc]) (by simp [hfcd]) ⟨by simp, fun x _ _ => by simp⟩
  have hS' : S' = st f ((List.range n).flatMap blk ++ o) := by
    funext k
    rcases k with _ | x
    · rw [h'o, Nat.sub_self, ← List.range_eq_range']; rfl
    · by_cases hx1 : x = c
      · subst hx1; rw [h'c]; simp [hfc]
      · by_cases hx2 : x = cd
        · subst hx2; rw [h'cd]; simp [hfcd]
        · exact List.eq_replicate_iff.2 ⟨h'x x hx1 hx2, fun _ _ => rfl⟩
  rw [hS'] at hrun
  exact hrun

end View

section Addu

variable {C : Type} [DecidableEq C]

theorem emitR_st (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (List.replicate n () ++ st f o (.c x)) =
      st (update f x (n + f x)) o := by
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c]

theorem addU_st_single (f : C → ℕ) (o : List Bool) (y : C) (n : ℕ) :
    addU [⟨.c y, ()⟩] n (st f o) = st (update f y (n + f y)) o := by
  funext k
  rcases k with _ | z
  · rw [addU_single_ne _ _ _ (by simp)]; rfl
  · by_cases h : z = y
    · subst h; rw [addU_single_self]; simp
    · rw [addU_single_ne _ _ _ (by simpa using h)]; simp [update_of_ne h]

theorem addU_st_pair (f : C → ℕ) (o : List Bool) (y z : C) (hyz : y ≠ z) (n : ℕ) :
    addU [⟨.c y, ()⟩, ⟨.c z, ()⟩] n (st f o) =
      st (update (update f y (n + f y)) z (n + f z)) o := by
  funext k
  rcases k with _ | w
  · rw [addU_pair_ne _ _ _ _ (by simp) (by simp)]; rfl
  · by_cases h : w = y
    · subst h; rw [addU_pair_fst]; simp [update_of_ne hyz]
    · by_cases h' : w = z
      · subst h'; rw [addU_pair_snd _ _ _ _ (by simpa using hyz.symm)]; simp
      · rw [addU_pair_ne _ _ _ _ (by simpa using h) (by simpa using h')]
        simp [update_of_ne h, update_of_ne h']

end Addu

end Cslib.Complexity.CookLevin.CounterView

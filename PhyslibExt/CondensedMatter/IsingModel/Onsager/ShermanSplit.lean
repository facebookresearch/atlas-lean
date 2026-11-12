/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.List.TakeWhile
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!

# Splitting rooted walks at returns to the root

Edge weights of walks given as lists, and the bijection between rooted closed walks and lists of
first-return segments.

## i. Overview

A walk is a list of directed edges `[e₀, e₁, …, eₖ]` with edge weight `Λ e₀ e₁ ⋯ Λ eₖ₋₁ eₖ`. A
closed walk starting and ending at `e` is cut at each return to `e` into first-return segments
`e, …, e` that do not meet `e` in their interior. `ons_glue` puts the segments back together, and
the two operations are mutually inverse. Edge weights multiply along the decomposition, and the
number of segments is the number of visits to `e`.

## ii. Key results

- `ons_edgeWeight` : the weight of a walk given as a list
- `ons_edgeWeight_glue` : weights multiply when segments are glued
- `ons_firstReturnSplit_glue` : splitting a glued list recovers the segments
- `ons_firstReturnFactors_spec` : every rooted closed walk is the gluing of its first-return factors
- `ons_count_glue_firstReturn` : the number of visits to the root is the number of segments plus one

## iii. Table of contents

- A. Edge weights of lists
- B. Gluing segments
- C. Splitting at first returns

## iv. References

- S. Sherman, *Combinatorial aspects of the Ising model for ferromagnetism. I. A conjecture of
  Feynman on paths and graphs*, J. Math. Phys. 1 (1960) 202-217

-/

@[expose] public section

namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section EdgeWeight

variable {E : Type*}

/-! ## A. Edge weights of lists -/

/-- The edge weight `Λ e₀ e₁ * Λ e₁ e₂ * ⋯ * Λ eₖ₋₁ eₖ` of a walk `[e₀, …, eₖ]`; walks with at most
one entry have weight `1`. -/
noncomputable def ons_edgeWeight (Λ : Matrix E E ℂ) : List E → ℂ
  | [] => 1
  | [_] => 1
  | a :: b :: t => Λ a b * ons_edgeWeight Λ (b :: t)

variable (Λ : Matrix E E ℂ)

@[simp] lemma ons_edgeWeight_nil : ons_edgeWeight Λ ([] : List E) = 1 := rfl

@[simp] lemma ons_edgeWeight_singleton (a : E) : ons_edgeWeight Λ [a] = 1 := rfl

lemma ons_edgeWeight_cons_cons (a b : E) (t : List E) :
    ons_edgeWeight Λ (a :: b :: t) = Λ a b * ons_edgeWeight Λ (b :: t) := rfl

lemma ons_edgeWeight_append_cons (u : List E) (b : E) (v : List E) :
    ons_edgeWeight Λ (u ++ b :: v)
      = ons_edgeWeight Λ (u ++ [b]) * ons_edgeWeight Λ (b :: v) := by
  induction u with
  | nil => simp
  | cons a u' ih =>
    cases u' with
    | nil =>
        change ons_edgeWeight Λ (a :: b :: v)
              = ons_edgeWeight Λ [a, b] * ons_edgeWeight Λ (b :: v)
        rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons, ons_edgeWeight_singleton]
        ring
    | cons c u'' =>
        change ons_edgeWeight Λ (a :: c :: (u'' ++ b :: v))
              = ons_edgeWeight Λ (a :: c :: (u'' ++ [b])) * ons_edgeWeight Λ (b :: v)
        rw [ons_edgeWeight_cons_cons, ons_edgeWeight_cons_cons]
        rw [show ons_edgeWeight Λ (c :: (u'' ++ b :: v))
              = ons_edgeWeight Λ (c :: (u'' ++ [b])) * ons_edgeWeight Λ (b :: v) from ih]
        ring

end EdgeWeight

section Glue

variable {E : Type*}

/-! ## B. Gluing segments -/

/-- Concatenation of walk segments sharing their end points at `e`: each segment except the last
loses its final entry, and the result ends in `e`. -/
def ons_glue (e : E) (ss : List (List E)) : List E :=
  ss.foldr (fun s acc => s.dropLast ++ acc) [e]

@[simp] lemma ons_glue_nil (e : E) : ons_glue e [] = [e] := rfl

lemma ons_glue_cons (e : E) (s : List E) (ss : List (List E)) :
    ons_glue e (s :: ss) = s.dropLast ++ ons_glue e ss := rfl

lemma ons_glue_head (e : E) (ss : List (List E))
    (hhead : ∀ s ∈ ss, s.head? = some e) :
    ∃ t, ons_glue e ss = e :: t := by
  induction ss with
  | nil => exact ⟨[], rfl⟩
  | cons s ss ih =>
    have hs : s.head? = some e := hhead s (by simp)
    obtain ⟨t, ht⟩ := ih (fun r hr => hhead r (by simp [hr]))
    rw [ons_glue_cons, ht]
    obtain ⟨s', hs'⟩ : ∃ s', s = e :: s' := by
      cases s with
      | nil => simp at hs
      | cons a s' =>
          rw [List.head?_cons, Option.some_inj] at hs
          exact ⟨s', by rw [hs]⟩
    subst hs'
    cases s' with
    | nil => exact ⟨t, rfl⟩
    | cons b s'' => exact ⟨(b :: s'').dropLast ++ e :: t, rfl⟩

lemma ons_edgeWeight_glue (Λ : Matrix E E ℂ) (e : E) (ss : List (List E))
    (hhead : ∀ s ∈ ss, s.head? = some e) (hlast : ∀ s ∈ ss, s.getLast? = some e) :
    ons_edgeWeight Λ (ons_glue e ss) = (ss.map (ons_edgeWeight Λ)).prod := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hsh : s.head? = some e := hhead s (by simp)
    have hsl : s.getLast? = some e := hlast s (by simp)
    have hhead' : ∀ r ∈ ss, r.head? = some e := fun r hr => hhead r (by simp [hr])
    have hlast' : ∀ r ∈ ss, r.getLast? = some e := fun r hr => hlast r (by simp [hr])
    obtain ⟨t, ht⟩ := ons_glue_head e ss hhead'
    have hsne : s ≠ [] := by
      rintro h; rw [h] at hsh; simp at hsh
    have hrecon : s.dropLast ++ [e] = s := List.dropLast_append_getLast? e hsl
    rw [ons_glue_cons, ht]
    rw [ons_edgeWeight_append_cons, ← ht, hrecon]
    rw [ih hhead' hlast']
    simp [List.map_cons]

end Glue

section Split

variable {E : Type*} [DecidableEq E]

/-! ## C. Splitting at first returns -/

/-- Splitting of a list at the occurrences of `e`: each piece runs from one occurrence of `e` to the
next. -/
def ons_firstReturnSplit (e : E) : List E → List (List E)
  | [] => []
  | x :: r =>
      match hpost : r.dropWhile (fun y => y ≠ e) with
      | [] => [x :: r]
      | e' :: post' =>
          (x :: r.takeWhile (fun y => y ≠ e) ++ [e']) :: ons_firstReturnSplit e (e' :: post')
  termination_by l => l.length
  decreasing_by
    have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
    rw [hpost] at hle
    simp only [List.length_cons] at hle ⊢
    omega

lemma ons_glue_firstReturnSplit (e : E) (w : List E) (hw : w.getLast? = some e) :
    ons_glue e (ons_firstReturnSplit e w) = w := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n → w.getLast? = some e →
      ons_glue e (ons_firstReturnSplit e w) = w := by
    intro n
    induction n with
    | zero =>
        intro w hlen hlast
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst hlen
        simp at hlast
    | succ n ih =>
        intro w hlen hlast
        obtain ⟨x, r, rfl⟩ : ∃ x r, w = x :: r := by
          cases w with
          | nil => simp at hlast
          | cons x r => exact ⟨x, r, rfl⟩
        rw [ons_firstReturnSplit]
        split
        · rw [ons_glue_cons, ons_glue_nil]
          exact List.dropLast_append_getLast? e hlast
        · rename_i e' post' hpost
          rw [ons_glue_cons]
          have hrne : r ≠ [] := by
            rintro rfl; simp at hpost
          have hgetr : r.getLast? = some e := by
            have : (x :: r).getLast? = r.getLast? := by
              rw [show x :: r = [x] ++ r from rfl]
              exact List.getLast?_append_of_ne_nil [x] hrne
            rw [← this]; exact hlast
          have hpne : e' :: post' ≠ [] := by simp
          have hgetsuf : (e' :: post').getLast? = some e := by
            rw [← hpost]
            have hsplit : r.takeWhile (fun y => y ≠ e) ++ r.dropWhile (fun y => y ≠ e) = r :=
              List.takeWhile_append_dropWhile
            have hdrop_ne : r.dropWhile (fun y => y ≠ e) ≠ [] := by rw [hpost]; simp
            calc (r.dropWhile (fun y => y ≠ e)).getLast?
                = (r.takeWhile (fun y => y ≠ e) ++ r.dropWhile (fun y => y ≠ e)).getLast? :=
                  (List.getLast?_append_of_ne_nil _ hdrop_ne).symm
              _ = r.getLast? := by rw [hsplit]
              _ = some e := hgetr
          have hlensuf : (e' :: post').length ≤ n := by
            have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
            rw [hpost] at hle
            simp only [List.length_cons] at hlen
            omega
          rw [ih (e' :: post') hlensuf hgetsuf]
          have hdl : (x :: r.takeWhile (fun y => y ≠ e) ++ [e']).dropLast
              = x :: r.takeWhile (fun y => y ≠ e) := by
            rw [show (x :: r.takeWhile (fun y => y ≠ e) ++ [e'])
                  = (x :: r.takeWhile (fun y => y ≠ e)) ++ [e'] from rfl]
            exact List.dropLast_concat
          rw [hdl]
          rw [show x :: r.takeWhile (fun y => y ≠ e) ++ (e' :: post')
                = x :: (r.takeWhile (fun y => y ≠ e) ++ (e' :: post')) from rfl]
          rw [← hpost, List.takeWhile_append_dropWhile]
  exact key w.length w le_rfl hw

/-- A first-return segment at `e`: a list `e :: interior ++ [e]` whose interior avoids `e`. -/
def ons_isFirstReturnSegment (e : E) (s : List E) : Prop :=
  ∃ interior : List E,
    s = e :: interior ++ [e] ∧ ∀ x ∈ interior, x ≠ e

lemma ons_firstReturnSegment_head {e : E} {s : List E}
    (hs : ons_isFirstReturnSegment e s) : s.head? = some e := by
  obtain ⟨interior, rfl, _⟩ := hs
  simp

lemma ons_firstReturnSegment_last {e : E} {s : List E}
    (hs : ons_isFirstReturnSegment e s) : s.getLast? = some e := by
  obtain ⟨interior, rfl, _⟩ := hs
  rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
  exact List.getLast?_concat

private lemma takeWhile_ne_eq_self (e : E) (l : List E)
    (h : ∀ x ∈ l, x ≠ e) : l.takeWhile (fun x => x ≠ e) = l :=
  List.takeWhile_eq_self_iff.mpr fun x hx => decide_eq_true (h x hx)

private lemma dropWhile_ne_eq_nil (e : E) (l : List E)
    (h : ∀ x ∈ l, x ≠ e) : l.dropWhile (fun x => x ≠ e) = [] :=
  List.dropWhile_eq_nil_iff.mpr fun x hx => decide_eq_true (h x hx)

private lemma dropWhile_head_eq_root (e : E) {l : List E} {x : E} {xs : List E}
    (h : l.dropWhile (fun y => y ≠ e) = x :: xs) : x = e := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      rw [List.dropWhile_cons] at h
      by_cases hy : y ≠ e
      · have hyb : decide (y ≠ e) = true := by simp [hy]
        rw [ite_eq_left hyb] at h
        exact ih h
      · have hyb : ¬ decide (y ≠ e) = true := by simp [hy]
        rw [ite_eq_right hyb] at h
        have hy' : y = e := not_ne_iff.mp hy
        injection h with hxy _
        exact hxy.symm.trans hy'

lemma ons_firstReturnSplit_glue (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
    ons_firstReturnSplit e (ons_glue e ss) = ss ++ [[e]] := by
  induction ss with
  | nil => simp [ons_firstReturnSplit]
  | cons s ss ih =>
      have hs := hfirst s (by simp)
      obtain ⟨interior, hsform, hinterior⟩ := hs
      subst s
      have hfirst' : ∀ t ∈ ss, ons_isFirstReturnSegment e t := by
        intro t ht
        exact hfirst t (by simp [ht])
      have hhead : ∀ t ∈ ss, t.head? = some e := by
        intro t ht
        exact ons_firstReturnSegment_head (hfirst' t ht)
      obtain ⟨tail, hglue⟩ := ons_glue_head e ss hhead
      have htake : interior.takeWhile (fun x => x ≠ e) = interior :=
        takeWhile_ne_eq_self e interior hinterior
      have hdrop : interior.dropWhile (fun x => x ≠ e) = [] :=
        dropWhile_ne_eq_nil e interior hinterior
      have htakeAll :
          (interior ++ e :: tail).takeWhile (fun x => x ≠ e) = interior := by
        rw [List.takeWhile_append, htake]
        simp
      have hdropAll :
          (interior ++ e :: tail).dropWhile (fun x => x ≠ e) = e :: tail := by
        rw [List.dropWhile_append, hdrop]
        simp
      rw [ons_glue_cons]
      have hdl : (e :: interior ++ [e]).dropLast = e :: interior := by
        rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
        exact List.dropLast_concat
      rw [hdl, hglue]
      change ons_firstReturnSplit e (e :: (interior ++ e :: tail)) = _
      rw [ons_firstReturnSplit]
      rw [hdropAll]
      simp only [htakeAll]
      rw [← hglue, ih hfirst']
      simp

lemma ons_firstReturnSplit_closed (e : E) (w : List E)
    (hhead : w.head? = some e) (hlast : w.getLast? = some e) :
    ∃ ss : List (List E),
      ons_firstReturnSplit e w = ss ++ [[e]] ∧
      ∀ s ∈ ss, ons_isFirstReturnSegment e s := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n → w.head? = some e →
      w.getLast? = some e →
      ∃ ss : List (List E),
        ons_firstReturnSplit e w = ss ++ [[e]] ∧
        ∀ s ∈ ss, ons_isFirstReturnSegment e s := by
    intro n
    induction n with
    | zero =>
        intro w hlen hhead _
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst w
        simp at hhead
    | succ n ih =>
        intro w hlen hhead hlast
        obtain ⟨x, r, rfl⟩ : ∃ x r, w = x :: r := by
          cases w with
          | nil => simp at hhead
          | cons x r => exact ⟨x, r, rfl⟩
        have hx : x = e := by simpa using hhead
        subst x
        rw [ons_firstReturnSplit]
        split
        · rename_i hpost
          have hr : r = [] := by
            by_contra hrne
            obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
              cases r with
              | nil => exact absurd rfl hrne
              | cons y ys => exact ⟨y, ys, rfl⟩
            have hlast' : (y :: ys).getLast? = some e := by
              simpa only [List.getLast?_cons_cons] using hlast
            obtain ⟨zs, hzs⟩ := List.getLast?_eq_some_iff.mp hlast'
            have hemem : e ∈ y :: ys := by
              rw [hzs]
              simp
            have hall := (List.dropWhile_eq_nil_iff.mp hpost) e hemem
            simp at hall
          subst r
          exact ⟨[], by simp, by simp⟩
        · rename_i e' post hpost
          have he' : e' = e := dropWhile_head_eq_root e hpost
          subst e'
          have hsegment : ons_isFirstReturnSegment e
              (e :: r.takeWhile (fun y => y ≠ e) ++ [e]) := by
            refine ⟨r.takeWhile (fun y => y ≠ e), rfl, ?_⟩
            intro y hy
            have hy' : decide (y ≠ e) = true :=
              List.mem_takeWhile_imp (p := fun z : E => decide (z ≠ e)) hy
            exact of_decide_eq_true hy'
          have hrne : r ≠ [] := by
            rintro rfl
            simp at hpost
          have hgetr : r.getLast? = some e := by
            have hlastCons : (e :: r).getLast? = r.getLast? := by
              rw [show e :: r = [e] ++ r from rfl]
              exact List.getLast?_append_of_ne_nil [e] hrne
            rw [← hlastCons]
            exact hlast
          have hsufLast : (e :: post).getLast? = some e := by
            rw [← hpost]
            have hdropNe : r.dropWhile (fun y => y ≠ e) ≠ [] := by
              rw [hpost]
              simp
            calc
              (r.dropWhile (fun y => y ≠ e)).getLast? =
                  (r.takeWhile (fun y => y ≠ e) ++
                    r.dropWhile (fun y => y ≠ e)).getLast? :=
                (List.getLast?_append_of_ne_nil _ hdropNe).symm
              _ = r.getLast? := by rw [List.takeWhile_append_dropWhile]
              _ = some e := hgetr
          have hsufLen : (e :: post).length ≤ n := by
            have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
            rw [hpost] at hle
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨ss, hsplit, hvalid⟩ :=
            ih (e :: post) hsufLen (by simp) hsufLast
          refine ⟨(e :: r.takeWhile (fun y => y ≠ e) ++ [e]) :: ss, ?_, ?_⟩
          · rw [hsplit]
            rfl
          · intro s hs
            simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · exact hsegment
            · exact hvalid s hs
  exact key w.length w le_rfl hhead hlast

private lemma list_count_eq_sum_indicator (e : E) (l : List E) :
    l.count e = (l.map fun x => if x = e then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.count_cons, List.map_cons, List.sum_cons, ih]
      by_cases hx : x = e <;> simp [hx, beq_iff_eq] <;> omega

lemma ons_count_ofFn_eq_visitCount (e : E) {n : ℕ} (v : Fin n → E) :
    (List.ofFn v).count e = Fintype.card {k : Fin n // v k = e} := by
  rw [list_count_eq_sum_indicator, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin n, if v k = e then 1 else 0) = _
  rw [Finset.sum_boole]
  rw [← Finset.card_subtype]
  simp

lemma ons_glue_append_terminal (e : E) (ss : List (List E)) :
    ons_glue e (ss ++ [[e]]) = ons_glue e ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      rw [List.cons_append, ons_glue_cons, ons_glue_cons, ih]

lemma ons_count_glue_firstReturn (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
    (ons_glue e ss).count e = ss.length + 1 := by
  induction ss with
  | nil => simp [ons_glue]
  | cons s ss ih =>
      have hs := hfirst s (by simp)
      obtain ⟨interior, hsform, hinterior⟩ := hs
      subst s
      have hfirst' : ∀ t ∈ ss, ons_isFirstReturnSegment e t := by
        intro t ht
        exact hfirst t (by simp [ht])
      have hcountInterior : interior.count e = 0 := by
        rw [List.count_eq_zero]
        intro he
        exact hinterior e he rfl
      rw [ons_glue_cons]
      have hdl : (e :: interior ++ [e]).dropLast = e :: interior := by
        rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
        exact List.dropLast_concat
      rw [hdl, List.count_append, List.count_cons, hcountInterior, ih hfirst']
      simp
      omega

/-- The first-return segments of a closed walk at `e`, without the trailing one-element piece `[e]`.
-/
def ons_firstReturnFactors (e : E) (w : List E) : List (List E) :=
  (ons_firstReturnSplit e w).dropLast

lemma ons_firstReturnFactors_spec (e : E) (w : List E)
    (hhead : w.head? = some e) (hlast : w.getLast? = some e) :
    ons_firstReturnSplit e w = ons_firstReturnFactors e w ++ [[e]] ∧
    (∀ s ∈ ons_firstReturnFactors e w, ons_isFirstReturnSegment e s) ∧
    ons_glue e (ons_firstReturnFactors e w) = w := by
  obtain ⟨ss, hsplit, hvalid⟩ := ons_firstReturnSplit_closed e w hhead hlast
  have hfactors : ons_firstReturnFactors e w = ss := by
    unfold ons_firstReturnFactors
    rw [hsplit]
    simp
  rw [hfactors]
  refine ⟨hsplit, hvalid, ?_⟩
  rw [← ons_glue_append_terminal]
  rw [← hsplit]
  exact ons_glue_firstReturnSplit e w hlast

lemma ons_edgeWeight_firstReturnSplit (Λ : Matrix E E ℂ) (e : E) (w : List E) :
    ((ons_firstReturnSplit e w).map (ons_edgeWeight Λ)).prod = ons_edgeWeight Λ w := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n →
      ((ons_firstReturnSplit e w).map (ons_edgeWeight Λ)).prod = ons_edgeWeight Λ w := by
    intro n
    induction n with
    | zero =>
        intro w hlen
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst hlen
        simp [ons_firstReturnSplit]
    | succ n ih =>
        intro w hlen
        cases w with
        | nil => simp [ons_firstReturnSplit]
        | cons x r =>
          rw [ons_firstReturnSplit]
          split
          · simp
          · rename_i e' post' hpost
            rw [List.map_cons, List.prod_cons]
            have hlensuf : (e' :: post').length ≤ n := by
              have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
              rw [hpost] at hle
              simp only [List.length_cons] at hlen
              omega
            rw [ih (e' :: post') hlensuf]
            have hsplit : r.takeWhile (fun y => y ≠ e) ++ (e' :: post') = r := by
              rw [← hpost]; exact List.takeWhile_append_dropWhile
            have hxr : x :: r.takeWhile (fun y => y ≠ e) ++ (e' :: post') = x :: r := by
              rw [List.cons_append, hsplit]
            have hrw : ons_edgeWeight Λ (x :: r)
                = ons_edgeWeight Λ (x :: r.takeWhile (fun y => y ≠ e) ++ [e'])
                    * ons_edgeWeight Λ (e' :: post') := by
              rw [← hxr, ons_edgeWeight_append_cons]
            rw [hrw]
  exact key w.length w le_rfl

end Split

end StatMech.Onsager

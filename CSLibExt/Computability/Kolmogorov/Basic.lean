/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kolmogorov complexity
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Kolmogorov complexity

The **Kolmogorov complexity** `K x` of a binary string `x` is the length of a shortest
description of `x` (Sipser, §6.4). Descriptions are read by a fixed universal description method
`U` built on Mathlib's `Nat.Partrec.Code`:

* `run c w` runs the code `c` on the string `w`, with strings passed through their encodings as
  natural numbers;
* the description `describe c w = 1ⁿ 0 w`, where `n` is the number of `c`, makes `U` run `c` on
  `w` (`U_describe`). The prefix `1ⁿ 0` is self-delimiting, so `U` can split it off.

Then:

* `K_le_length_add`: `K x ≤ |x| + c`, by the code of the identity;
* `exists_K_le_of_partrec` (**optimality**, the invariance theorem): for every partial recursive
  description method `D` there is a constant `c` such that `K x ≤ |p| + c` whenever `D p = x`.
  `U` simulates `D` through a code for it;
* `K_append_self_le`: `K (x ++ x) ≤ K x + c`, by optimality for "decode, then double";
* `K_append_le`: `K (x ++ y) ≤ 2 K x + K y + c`, by optimality for the pair descriptions
  `1^|p| 0 p q` (`pairU`).

## Main definitions

- `run`, `describe`, `U`, `K`, `pairDescribe`, `pairU`.

## Main results

- `U_describe`, `K_le`, `exists_length_eq_K`, `partrec_U`.
- `K_le_length_add`, `exists_K_le_of_partrec`, `K_append_self_le`, `K_append_le`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §6.4.
* M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th ed.,
  Springer, 2019, Chapter 2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Kolmogorov

open Encodable Denumerable
open Nat.Partrec (Code)

/-- Run a code on a binary string; the input and output strings go through their encodings as
natural numbers. -/
def run (c : Code) (w : List Bool) : Part (List Bool) :=
  (c.eval (encode w)).bind fun n ↦ Part.ofOption (decode n)

/-- The description `1ⁿ 0 w` of the code `c` with number `n` running on `w`. -/
def describe (c : Code) (w : List Bool) : List Bool :=
  List.replicate (encode c) true ++ false :: w

/-- **The universal description method.** A description `1ⁿ 0 w` runs code number `n` on `w`;
a string of `1`s describes nothing. -/
def U (p : List Bool) : Part (List Bool) :=
  (Part.ofOption (p.dropWhile id).head?).bind fun _ ↦
    run (ofNat Code (p.takeWhile id).length) (p.dropWhile id).tail

@[simp]
theorem U_describe (c : Code) (w : List Bool) : U (describe c w) = run c w := by
  simp [U, describe]

@[simp]
theorem length_describe (c : Code) (w : List Bool) :
    (describe c w).length = encode c + 1 + w.length := by
  simp [describe]
  omega

theorem run_id (w : List Bool) : run Code.id w = Part.some w := by
  simp [run, Code.eval_id]

theorem exists_mem_U (x : List Bool) : ∃ p, x ∈ U p :=
  ⟨describe Code.id x, by simp [run_id]⟩

open Classical in
/-- **Kolmogorov complexity**: the length of a shortest description of `x`. -/
noncomputable def K (x : List Bool) : ℕ :=
  Nat.find (⟨_, (exists_mem_U x).choose, rfl, (exists_mem_U x).choose_spec⟩ :
    ∃ n, ∃ p : List Bool, p.length = n ∧ x ∈ U p)

/-- A description bounds the complexity. -/
theorem K_le {x p : List Bool} (h : x ∈ U p) : K x ≤ p.length := by
  classical
  exact Nat.find_min' _ ⟨p, rfl, h⟩

/-- A shortest description. -/
theorem exists_length_eq_K (x : List Bool) : ∃ p : List Bool, p.length = K x ∧ x ∈ U p := by
  classical
  exact Nat.find_spec (⟨_, (exists_mem_U x).choose, rfl, (exists_mem_U x).choose_spec⟩ :
    ∃ n, ∃ p : List Bool, p.length = n ∧ x ∈ U p)

/-- **Complexity is at most the length plus a constant**: `K x ≤ |x| + c`. -/
theorem K_le_length_add : ∃ c, ∀ x : List Bool, K x ≤ x.length + c :=
  ⟨encode Code.id + 1, fun x ↦ by
    have := K_le (x := x) (p := describe Code.id x) (by simp [run_id])
    simp only [length_describe] at this
    omega⟩

theorem partrec₂_run : Partrec₂ run :=
  Partrec.bind (Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd))
    (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂

/-- The universal description method is partial recursive. -/
theorem partrec_U : Partrec U :=
  Partrec.bind (Computable.ofOption
    (Primrec.list_head?.comp (Primrec.list_dropWhile Primrec.id)).to_comp)
    (partrec₂_run.comp
      (((Primrec.ofNat Code).comp (Primrec.list_length.comp
        (Primrec.list_takeWhile Primrec.id))).to_comp.comp Computable.fst)
      ((Primrec.list_tail.comp (Primrec.list_dropWhile Primrec.id)).to_comp.comp
        Computable.fst)).to₂

/-- Every partial recursive description method is run by some code. -/
theorem exists_run_eq {D : List Bool →. List Bool} (hD : Partrec D) : ∃ c : Code, run c = D := by
  have hG : Partrec fun n : ℕ ↦ (Part.ofOption (decode (α := List Bool) n)).bind fun w ↦
      (D w).map encode :=
    Partrec.bind (Computable.ofOption Computable.decode)
      ((hD.comp Computable.snd).map (Computable.encode.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hG)
  refine ⟨c, funext fun w ↦ Part.ext fun x ↦ ?_⟩
  simp [run, hc]

/-- **Optimality** (the invariance theorem): the universal description method is at most a
constant worse than any partial recursive description method `D`. -/
theorem exists_K_le_of_partrec {D : List Bool →. List Bool} (hD : Partrec D) :
    ∃ c, ∀ x p : List Bool, x ∈ D p → K x ≤ p.length + c := by
  obtain ⟨cD, hcD⟩ := exists_run_eq hD
  refine ⟨encode cD + 1, fun x p hx ↦ ?_⟩
  have := K_le (p := describe cD p) (by rw [U_describe, hcD]; exact hx)
  simp only [length_describe] at this
  omega

/-- **Doubling costs a constant**: `K (x ++ x) ≤ K x + c`. -/
theorem K_append_self_le : ∃ c, ∀ x : List Bool, K (x ++ x) ≤ K x + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec
    (D := fun p ↦ (U p).map fun x ↦ x ++ x)
    (partrec_U.map (Primrec.list_append.comp Primrec.snd Primrec.snd).to_comp.to₂)
  refine ⟨c, fun x ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := exists_length_eq_K x
  rw [← hp]
  exact hc _ p (Part.mem_map _ hx)

/-- The pair description `1^|p| 0 p q`, read by `pairU` as the concatenation of what `p` and `q`
describe. -/
def pairDescribe (p q : List Bool) : List Bool := List.replicate p.length true ++ false :: (p ++ q)

/-- Read a pair description `1ⁿ 0 r` as the concatenation of what the first `n` letters of `r`
and the rest describe. -/
def pairU (s : List Bool) : Part (List Bool) :=
  (U (((s.dropWhile id).tail).take (s.takeWhile id).length)).bind fun x ↦
    (U (((s.dropWhile id).tail).drop (s.takeWhile id).length)).map fun y ↦ x ++ y

theorem takeWhile_replicate_true (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).takeWhile id = List.replicate n true := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem dropWhile_replicate_true (n : ℕ) (r : List Bool) :
    (List.replicate n true ++ false :: r).dropWhile id = false :: r := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem pairU_pairDescribe {p q x y : List Bool} (hx : x ∈ U p) (hy : y ∈ U q) :
    x ++ y ∈ pairU (pairDescribe p q) := by
  rw [pairU, pairDescribe, takeWhile_replicate_true, dropWhile_replicate_true]
  simp only [List.tail_cons, List.length_replicate, List.take_left', List.drop_left']
  exact Part.mem_bind_iff.mpr ⟨x, hx, Part.mem_map _ hy⟩

theorem partrec_pairU : Partrec pairU := by
  have hlen : Primrec fun s : List Bool ↦ (s.takeWhile id).length :=
    Primrec.list_length.comp (Primrec.list_takeWhile Primrec.id)
  have hrest : Primrec fun s : List Bool ↦ (s.dropWhile id).tail :=
    Primrec.list_tail.comp (Primrec.list_dropWhile Primrec.id)
  exact Partrec.bind (partrec_U.comp (Primrec.list_take.comp hlen hrest).to_comp)
    ((partrec_U.comp ((Primrec.list_drop.comp hlen hrest).to_comp.comp Computable.fst)).map
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to_comp.to₂).to₂

/-- **Concatenation costs at most twice the first part**: `K (x ++ y) ≤ 2 K x + K y + c`. -/
theorem K_append_le : ∃ c, ∀ x y : List Bool, K (x ++ y) ≤ 2 * K x + K y + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec partrec_pairU
  refine ⟨c + 1, fun x y ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := exists_length_eq_K x
  obtain ⟨q, hq, hy⟩ := exists_length_eq_K y
  have := hc _ _ (pairU_pairDescribe hx hy)
  simp only [pairDescribe, List.length_append, List.length_replicate, List.length_cons] at this
  omega

end Cslib.Kolmogorov

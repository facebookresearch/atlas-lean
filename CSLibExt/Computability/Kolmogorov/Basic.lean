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

/-- **Running a program on a binary string.** For a code $c$ of a partial recursive function on
the natural numbers and a binary string $w$, running $c$ on $w$ evaluates $c$ at the number
encoding $w$; if this halts with output $m$, the result is the binary string encoded by $m$. The
result is undefined when the evaluation does not halt or $m$ encodes no binary string. -/
def run (c : Code) (w : List Bool) : Part (List Bool) :=
  (c.eval (encode w)).bind fun n ↦ Part.ofOption (decode n)

/-- **Description of a code running on an input.** Let $c$ be a code for a partial recursive
function and let $n$ be its number in the standard encoding of codes as natural numbers. For a
binary string $w$, the description of $c$ running on $w$ is the binary string $1^n 0 w$, that is,
$n$ ones, then a zero, then $w$. -/
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
/-- **Kolmogorov complexity.** The Kolmogorov complexity $K(x)$ of a binary string $x$ is the
least length of a binary string $p$ such that $U(p)$ is defined and equals $x$, where $U$ is the
universal description method. -/
noncomputable def K (x : List Bool) : ℕ :=
  Nat.find (⟨_, (exists_mem_U x).choose, rfl, (exists_mem_U x).choose_spec⟩ :
    ∃ n, ∃ p : List Bool, p.length = n ∧ x ∈ U p)

/-- **A description bounds the complexity.** Let $x$ and $p$ be binary strings such that $U(p)$ is
defined and equals $x$, where $U$ is the universal description method. Then the Kolmogorov
complexity of $x$ is at most the length of $p$: $K(x) \le |p|$. -/
theorem K_le {x p : List Bool} (h : x ∈ U p) : K x ≤ p.length := by
  classical
  exact Nat.find_min' _ ⟨p, rfl, h⟩

/-- **Shortest descriptions exist.** For every binary string $x$ there is a binary string $p$
whose length is the Kolmogorov complexity $K(x)$ and such that $U(p)$ is defined and equals $x$,
where $U$ is the universal description method. -/
theorem exists_length_eq_K (x : List Bool) : ∃ p : List Bool, p.length = K x ∧ x ∈ U p := by
  classical
  exact Nat.find_spec (⟨_, (exists_mem_U x).choose, rfl, (exists_mem_U x).choose_spec⟩ :
    ∃ n, ∃ p : List Bool, p.length = n ∧ x ∈ U p)

/-- **Complexity is at most the length plus a constant.** There is a natural number $c$ such that
every binary string $x$ satisfies $K(x) \le |x| + c$, where $K(x)$ is the Kolmogorov complexity
of $x$ and $|x|$ is its length. -/
theorem K_le_length_add : ∃ c, ∀ x : List Bool, K x ≤ x.length + c :=
  ⟨encode Code.id + 1, fun x ↦ by
    have := K_le (x := x) (p := describe Code.id x) (by simp [run_id])
    simp only [length_describe] at this
    omega⟩

theorem partrec₂_run : Partrec₂ run :=
  Partrec.bind (Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd))
    (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂

/-- **The universal description method is partial recursive.** The universal description
method, as a partial function from binary strings to binary strings, is partial recursive. -/
theorem partrec_U : Partrec U :=
  Partrec.bind (Computable.ofOption
    (Primrec.list_head?.comp (Primrec.list_dropWhile Primrec.id)).to_comp)
    (partrec₂_run.comp
      (((Primrec.ofNat Code).comp (Primrec.list_length.comp
        (Primrec.list_takeWhile Primrec.id))).to_comp.comp Computable.fst)
      ((Primrec.list_tail.comp (Primrec.list_dropWhile Primrec.id)).to_comp.comp
        Computable.fst)).to₂

/-- **Every partial recursive description method has a code.** Let $D$ be a partial recursive
function from binary strings to binary strings. Then there is a code $c$ for a partial recursive
function such that running $c$ equals $D$ as a partial function: for every binary string $w$,
running $c$ on $w$ is defined exactly when $D(w)$ is, and then has the same value. -/
theorem exists_run_eq {D : List Bool →. List Bool} (hD : Partrec D) : ∃ c : Code, run c = D := by
  have hG : Partrec fun n : ℕ ↦ (Part.ofOption (decode (α := List Bool) n)).bind fun w ↦
      (D w).map encode :=
    Partrec.bind (Computable.ofOption Computable.decode)
      ((hD.comp Computable.snd).map (Computable.encode.comp Computable.snd).to₂)
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hG)
  refine ⟨c, funext fun w ↦ Part.ext fun x ↦ ?_⟩
  simp [run, hc]

/-- **Optimality (the invariance theorem).** Let $D$ be a partial recursive function from binary
strings to binary strings, viewed as a description method. Then there is a natural number $c$
such that for all binary strings $x$ and $p$ for which $D(p)$ is defined and equals $x$, the
Kolmogorov complexity of $x$ satisfies $K(x) \le |p| + c$, where $|p|$ is the length of $p$. -/
theorem exists_K_le_of_partrec {D : List Bool →. List Bool} (hD : Partrec D) :
    ∃ c, ∀ x p : List Bool, x ∈ D p → K x ≤ p.length + c := by
  obtain ⟨cD, hcD⟩ := exists_run_eq hD
  refine ⟨encode cD + 1, fun x p hx ↦ ?_⟩
  have := K_le (p := describe cD p) (by rw [U_describe, hcD]; exact hx)
  simp only [length_describe] at this
  omega

/-- **Doubling costs a constant.** There is a natural number $c$ such that for every binary string
$x$, the Kolmogorov complexity of the concatenation $xx$ of $x$ with itself satisfies
$K(xx) \le K(x) + c$. -/
theorem K_append_self_le : ∃ c, ∀ x : List Bool, K (x ++ x) ≤ K x + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec
    (D := fun p ↦ (U p).map fun x ↦ x ++ x)
    (partrec_U.map (Primrec.list_append.comp Primrec.snd Primrec.snd).to_comp.to₂)
  refine ⟨c, fun x ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := exists_length_eq_K x
  rw [← hp]
  exact hc _ p (Part.mem_map _ hx)

/-- **Pair description.** For binary strings $p$ and $q$, the pair description of $p$ and $q$ is
the binary string $1^{|p|} 0 p q$, that is, $|p|$ ones, where $|p|$ is the length of $p$, then a
zero, then $p$, then $q$.

The prefix $1^{|p|} 0$ records the length of $p$, so the string splits back into $p$ and $q$. -/
def pairDescribe (p q : List Bool) : List Bool := List.replicate p.length true ++ false :: (p ++ q)

/-- **Reading pair descriptions.** Write a binary string $s$ as $1^n s'$, where $n$ is the number
of leading $1$s, and let $r$ be $s'$ without its first letter ($r$ is empty when $s'$ is). Let
$r_1$ be the first $\min(n, |r|)$ letters of $r$ and $r_2$ the remaining ones. The pair reader
maps $s$ to the concatenation $U(r_1)\,U(r_2)$, where $U$ is the universal description method,
and is undefined when $U(r_1)$ or $U(r_2)$ is undefined. On a pair description $1^n 0 r$ with
$|r| \ge n$, this is the concatenation of what the first $n$ letters of $r$ and the rest
describe. -/
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

/-- **Concatenation costs at most twice the first part.** There is a natural number $c$ such that
for all binary strings $x$ and $y$, the Kolmogorov complexity of their concatenation $xy$
satisfies $K(xy) \le 2K(x) + K(y) + c$. -/
theorem K_append_le : ∃ c, ∀ x y : List Bool, K (x ++ y) ≤ 2 * K x + K y + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec partrec_pairU
  refine ⟨c + 1, fun x y ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := exists_length_eq_K x
  obtain ⟨q, hq, hy⟩ := exists_length_eq_K y
  have := hc _ _ (pairU_pairDescribe hx hy)
  simp only [pairDescribe, List.length_append, List.length_replicate, List.length_cons] at this
  omega

end Cslib.Kolmogorov

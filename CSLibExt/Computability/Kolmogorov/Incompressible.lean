/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Incompressible strings, and Kolmogorov complexity is not computable
-/
module

public import CSLibExt.Computability.Kolmogorov.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Incompressible strings, and Kolmogorov complexity is not computable

* `card_lt_two_pow`: fewer than `2 ^ m` strings have complexity below `m`. Padding their
  shortest descriptions to length `m` as `0…0 1 p` maps them injectively to strings of length
  `m` other than `0ᵐ`.
* `card_compressible_lt`: fewer than `2 ^ (n - c)` strings of length `n` are compressible by
  `c`, and `exists_incompressible`: for every `n` there is a string of length `n` with
  `K x ≥ n`.
* `not_computable_K` (Berry's paradox): if `K` were computable, so would be the first string `g n`
  with `K (g n) ≥ n`. The description method `p ↦ g (2|p| + 1)` would then describe strings of
  complexity at least `2|p| + 1` by descriptions of length `|p|`, which optimality
  (`exists_K_le_of_partrec`) turns into `2|p| + 1 ≤ |p| + c`, false for `|p| = c + 1`.

## Main results

- `card_lt_two_pow`, `card_compressible_lt`, `exists_incompressible`, `not_computable_K`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §6.4.
* M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th ed.,
  Springer, 2019, Chapter 2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Kolmogorov

open Encodable

/-- **Padding a string to a given length.** For a natural number $n$ and a binary string $p$, the
padding of $p$ to length $n$ is the string $0^k 1 p$ with $k = \max(n - 1 - |p|, 0)$; when
$|p| < n$ it has length $n$. -/
def pad (n : ℕ) (p : List Bool) : List Bool := List.replicate (n - 1 - p.length) false ++ true :: p

theorem length_pad {n : ℕ} {p : List Bool} (h : p.length < n) : (pad n p).length = n := by
  simp [pad]
  omega

theorem eq_of_pad_eq {a b : ℕ} {p q : List Bool}
    (h : List.replicate a false ++ true :: p = List.replicate b false ++ true :: q) : p = q := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      exact ih h

/-- **Few strings have small complexity**: fewer than `2 ^ m` strings have complexity below `m`.
Padding their shortest descriptions to length `m` maps them injectively to strings of length `m`
other than `0ᵐ`. -/
theorem card_lt_two_pow {m : ℕ} (S : Finset (List Bool)) (hS : ∀ x ∈ S, K x < m) :
    S.card < 2 ^ m := by
  classical
  choose d hd using exists_length_eq_K
  let z : List.Vector Bool m := ⟨List.replicate m false, by simp⟩
  let f : List Bool → List.Vector Bool m := fun x ↦
    if h : K x < m then ⟨pad m (d x), length_pad (by rw [(hd x).1]; exact h)⟩ else z
  have hf : ∀ x ∈ S, (f x).1 = pad m (d x) := by
    intro x hx
    simp [f, hS x hx]
  have hmaps : ∀ x ∈ S, f x ∈ (Finset.univ : Finset (List.Vector Bool m)).erase z := by
    intro x hx
    refine Finset.mem_erase.mpr ⟨fun h ↦ ?_, Finset.mem_univ _⟩
    have htrue : true ∈ (f x).1 := by
      rw [hf x hx]
      simp [pad]
    rw [h] at htrue
    simp [z] at htrue
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    have h₁ : d x = d y :=
      eq_of_pad_eq ((hf x hx).symm.trans ((congrArg Subtype.val hxy).trans (hf y hy)))
    exact Part.mem_unique (hd x).2 (h₁ ▸ (hd y).2)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_vector,
    Fintype.card_bool] at hcard
  have : 0 < 2 ^ m := Nat.two_pow_pos m
  omega

/-- **Binary strings of a given length.** For a natural number $n$, the finite set of all binary
strings of length $n$. -/
noncomputable def stringsOfLength (n : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (List.Vector Bool n)).map
    ⟨List.Vector.toList, List.Vector.toList_injective⟩

theorem mem_stringsOfLength {n : ℕ} {x : List Bool} : x ∈ stringsOfLength n ↔ x.length = n := by
  constructor
  · intro h
    obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp h
    exact v.toList_length
  · intro h
    exact Finset.mem_map.mpr ⟨⟨x, h⟩, Finset.mem_univ _, rfl⟩

theorem card_stringsOfLength (n : ℕ) : (stringsOfLength n).card = 2 ^ n := by
  simp [stringsOfLength, card_vector]

/-- **Most strings are incompressible.** For all natural numbers $n$ and $c$, fewer than
$2^{n-c}$ binary strings of length $n$ have Kolmogorov complexity less than $n - c$, where
$n - c$ is read as $0$ when $c > n$.

Hence at least $2^n - 2^{n-c} + 1$ strings of length $n$ have complexity at least $n - c$. -/
theorem card_compressible_lt (n c : ℕ) :
    ((stringsOfLength n).filter fun x ↦ K x < n - c).card < 2 ^ (n - c) :=
  card_lt_two_pow _ fun _ hx ↦ (Finset.mem_filter.mp hx).2

/-- **Incompressible strings exist at every length**: some string of length `n` has complexity at
least `n`. -/
theorem exists_incompressible (n : ℕ) : ∃ x : List Bool, x.length = n ∧ n ≤ K x := by
  by_contra! H
  have := card_lt_two_pow (stringsOfLength n) fun x hx ↦ H x (mem_stringsOfLength.mp hx)
  rw [card_stringsOfLength] at this
  exact lt_irrefl _ this

/-- **Kolmogorov complexity is not computable.** The function sending each binary string $x$
to its Kolmogorov complexity $K(x)$ is not computable: no partial recursive function, acting on
binary strings through their encodings as natural numbers, halts on every binary string $x$ with
output $K(x)$.

The proof is a form of Berry's paradox. -/
theorem not_computable_K : ¬Computable K := by
  intro hK
  -- `test n m`: the string numbered `m` has complexity at least `n`
  let test : ℕ → ℕ → Bool := fun n m ↦
    (decode (α := List Bool) m).elim false fun x ↦ decide (n ≤ K x)
  have htest : Computable₂ test :=
    (Computable.option_casesOn (Computable.decode.comp Computable.snd) (Computable.const false)
      ((Primrec.nat_le.decide.to_comp.comp (Computable.fst.comp Computable.fst)
        (hK.comp Computable.snd)).to₂)).of_eq fun q ↦ by
      simp only [test]
      cases decode (α := List Bool) q.2 <;> rfl
  -- `g n`: the first string with complexity at least `n`
  let g : ℕ →. List Bool := fun n ↦
    (Nat.rfind fun m ↦ Part.some (test n m)).bind fun m ↦ Part.ofOption (decode m)
  have hg : Partrec g :=
    Partrec.bind (Partrec.rfind (htest.comp (Computable.fst) Computable.snd).partrec)
      (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂
  have hgspec : ∀ n, ∃ x ∈ g n, n ≤ K x := by
    intro n
    obtain ⟨x₀, -, hx₀⟩ := exists_incompressible n
    have hdom : (Nat.rfind fun m ↦ Part.some (test n m)).Dom :=
      Nat.rfind_dom.mpr ⟨encode x₀, by simp [test, hx₀], fun _ ↦ trivial⟩
    have hm := Part.get_mem hdom
    have hspec := Nat.rfind_spec hm
    simp only [Part.mem_some_iff] at hspec
    cases hdec : decode (α := List Bool) ((Nat.rfind fun m ↦ Part.some (test n m)).get hdom) with
    | none => simp [test, hdec] at hspec
    | some x =>
      refine ⟨x, Part.mem_bind_iff.mpr ⟨_, hm, by simp [hdec]⟩, ?_⟩
      simpa [test, hdec] using hspec.symm
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec (D := fun p ↦ g (2 * p.length + 1))
    (hg.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      Primrec.list_length) (Primrec.const 1)).to_comp)
  obtain ⟨x, hx, hKx⟩ := hgspec (2 * (c + 1) + 1)
  have := hc x (List.replicate (c + 1) true) (by simpa using hx)
  simp only [List.length_replicate] at this
  omega

end Cslib.Kolmogorov

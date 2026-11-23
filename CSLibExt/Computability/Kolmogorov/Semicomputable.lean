/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Upper semicomputability of Kolmogorov complexity, and incompressible strings
-/
module

public import CSLibExt.Computability.Kolmogorov.Incompressible
public import MathlibExt.Computability.RE

/-!
# Upper semicomputability of Kolmogorov complexity, and incompressible strings

* `rePred_K_le`: `K` is **upper semicomputable**. The relation `K x ≤ n` is recognizable: search
  for a description of length at most `n`.
* `exists_K_map_le`: a partial recursive map raises complexity by at most a constant,
  `K y ≤ K x + c` whenever `y ∈ f x`.
* `exists_shortest_incompressible`: shortest descriptions are
  incompressible up to a constant, `|p| ≤ K p + b`. A description of `p` followed by `U` describes
  `x`.
* `exists_bound_of_rePred_le_K` (**Chaitin's incompleteness theorem**, abstract form): a
  recognizable set of true lower bounds `n ≤ K x` has bounded `n`. Select a member with a bound
  above `2|p| + 1` (`MetaMathlibExt.REPred.exists_partrec_choose`) and apply optimality (Berry's
  paradox). So every computable lower bound of `K` is bounded
  (`exists_bound_of_computable_le_K`), and `K` is not lower semicomputable (`not_rePred_le_K`).
* `not_rePred_of_forall_incompressible`: no recognizable set of strings with arbitrarily long
  members consists of incompressible strings.
* `not_rePred_incompressible`, `not_computablePred_incompressible`: the set of incompressible
  strings `{x | |x| ≤ K x}` is neither recognizable nor decidable, since it has members of every
  length (`exists_incompressible`).

## Main results

- `rePred_K_le`, `exists_K_map_le`, `exists_shortest_incompressible`.
- `exists_bound_of_rePred_le_K`, `exists_bound_of_computable_le_K`, `not_rePred_le_K`.
- `not_rePred_of_forall_incompressible`, `not_rePred_incompressible`,
  `not_computablePred_incompressible`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §6.4.
* M. Li, P. Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th ed.,
  Springer, 2019, Chapter 2.
* G. J. Chaitin, *Information-theoretic limitations of formal systems*, J. ACM 21 (1974),
  403–424.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Kolmogorov

open Encodable

/-- **The description relation is recognizable.** Let $U$ be the universal description method.
The set of pairs $(x, p)$ of binary strings such that $U(p)$ is defined and equal to $x$ is
recursively enumerable (recognizable). -/
theorem rePred_mem_U : REPred fun q : List Bool × List Bool ↦ q.1 ∈ U q.2 := by
  have h : Partrec fun q : List Bool × List Bool ↦
      (U q.2).bind fun y ↦ bif decide (y = q.1) then Part.some 0 else Part.none :=
    Partrec.bind (partrec_U.comp Computable.snd) (Partrec.cond
      (Primrec.eq.decide.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).to_comp
      (Partrec.const' (Part.some 0)) Partrec.none)
  refine h.dom_re.of_eq fun q ↦ ?_
  constructor
  · intro hd
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨y, hy, hz'⟩ := Part.mem_bind_iff.mp hz
    by_cases hyq : y = q.1
    · exact hyq ▸ hy
    · simp [hyq] at hz'
  · intro hq
    exact Part.dom_iff_mem.mpr ⟨0, Part.mem_bind_iff.mpr ⟨q.1, hq, by simp⟩⟩

/-- **Kolmogorov complexity is upper semicomputable.** Let $K$ denote Kolmogorov complexity. The
set of pairs $(x, n)$ of a binary string $x$ and a natural number $n$ with $K(x) \le n$ is
recursively enumerable (recognizable). -/
theorem rePred_K_le : REPred fun q : List Bool × ℕ ↦ K q.1 ≤ q.2 := by
  have hlenB : Computable fun r : (List Bool × ℕ) × List Bool ↦ decide (r.2.length ≤ r.1.2) :=
    (Primrec.nat_le.decide.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to_comp
  have hlen : REPred fun r : (List Bool × ℕ) × List Bool ↦ r.2.length ≤ r.1.2 :=
    ComputablePred.to_re ⟨fun _ ↦ inferInstance, hlenB⟩
  have hmem : REPred fun r : (List Bool × ℕ) × List Bool ↦ r.1.1 ∈ U r.2 :=
    Partrec.comp (g := fun r : (List Bool × ℕ) × List Bool ↦ (r.1.1, r.2)) rePred_mem_U
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hR : REPred fun r : (List Bool × ℕ) × List Bool ↦ r.2.length ≤ r.1.2 ∧ r.1.1 ∈ U r.2 :=
    MetaMathlibExt.REPred.and hlen hmem
  have hex := MetaMathlibExt.REPred.exists (R := fun (q : List Bool × ℕ) (p : List Bool) ↦
    p.length ≤ q.2 ∧ q.1 ∈ U p) hR
  refine hex.of_eq fun q ↦ ?_
  constructor
  · rintro ⟨p, hp, hx⟩
    exact (K_le hx).trans hp
  · intro h
    obtain ⟨p, hp, hx⟩ := exists_length_eq_K q.1
    exact ⟨p, hp.le.trans h, hx⟩

/-- **A partial recursive map raises complexity by at most a constant.** Let $K$ denote Kolmogorov
complexity and let $f$ be a partial recursive function from binary strings to binary strings.
Then there is a natural number $c$ such that $K(y) \le K(x) + c$ for all binary strings $x$ and
$y$ such that $f(x)$ is defined and equal to $y$. -/
theorem exists_K_map_le {f : List Bool →. List Bool} (hf : Partrec f) :
    ∃ c, ∀ x y : List Bool, y ∈ f x → K y ≤ K x + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec (D := fun p ↦ (U p).bind f)
    (Partrec.bind partrec_U (hf.comp Computable.snd))
  refine ⟨c, fun x y hy ↦ ?_⟩
  obtain ⟨p, hp, hx⟩ := exists_length_eq_K x
  rw [← hp]
  exact hc y p (Part.mem_bind_iff.mpr ⟨x, hx, hy⟩)

/-- **Shortest descriptions are incompressible.** Let $U$ be the universal description method,
$K$ Kolmogorov complexity, and $|p|$ the length of a binary string $p$. There is a natural number
$b$ such that for all binary strings $x$ and $p$, if $p$ is a shortest description of $x$, that
is, $U(p)$ is defined and equal to $x$ and $|p| = K(x)$, then $|p| \le K(p) + b$. -/
theorem exists_shortest_incompressible :
    ∃ b, ∀ x p : List Bool, p.length = K x → x ∈ U p → p.length ≤ K p + b := by
  obtain ⟨b, hb⟩ := exists_K_map_le partrec_U
  exact ⟨b, fun x p hp hx ↦ hp.le.trans (hb p x hx)⟩

/-- **Chaitin's incompleteness theorem.** Let $K$ denote Kolmogorov complexity, and let $S$ be a
recursively enumerable (recognizable) set of pairs $(x, n)$ of a binary string $x$ and a natural
number $n$ such that $n \le K(x)$ for every $(x, n) \in S$. Then there is a natural number $B$
with $n \le B$ for every $(x, n) \in S$.

This is the abstract form of the theorem: think of $S$ as the statements $K(x) \ge n$ that a sound
formal system proves. The proof searches $S$ for a pair with a large bound $n$ and applies
optimality of the universal description method (Berry's paradox). -/
theorem exists_bound_of_rePred_le_K {S : List Bool × ℕ → Prop} (hS : REPred S)
    (hsound : ∀ q, S q → q.2 ≤ K q.1) : ∃ B, ∀ q, S q → q.2 ≤ B := by
  by_contra! H
  -- `R n q`: `q` is in `S` with a bound of at least `n`
  have hR : REPred fun p : ℕ × (List Bool × ℕ) ↦ S p.2 ∧ p.1 ≤ p.2.2 :=
    MetaMathlibExt.REPred.and (Partrec.comp (g := fun p : ℕ × (List Bool × ℕ) ↦ p.2) hS
      Computable.snd)
      (ComputablePred.to_re ⟨inferInstance, (Primrec.nat_le.decide.comp Primrec.fst
        (Primrec.snd.comp Primrec.snd)).to_comp⟩)
  obtain ⟨g, hg, hgs, hgd⟩ :=
    MetaMathlibExt.REPred.exists_partrec_choose (R := fun n q ↦ S q ∧ n ≤ q.2) hR
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec (D := fun p ↦ (g (2 * p.length + 1)).map Prod.fst)
    ((hg.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      Primrec.list_length) (Primrec.const 1)).to_comp).map (Computable.fst.comp
        Computable.snd).to₂)
  obtain ⟨q, hq, hnq⟩ := H (2 * (c + 1) + 1)
  obtain ⟨q', hq'⟩ := Part.dom_iff_mem.mp (hgd _ ⟨q, hq, hnq.le⟩)
  obtain ⟨hSq', hle⟩ := hgs _ q' hq'
  have hK := hc q'.1 (List.replicate (c + 1) true) (by simpa using Part.mem_map Prod.fst hq')
  have := hsound q' hSq'
  simp only [List.length_replicate] at hK
  omega

/-- **A computable lower bound of Kolmogorov complexity is bounded.** Let $K$ denote Kolmogorov
complexity. If $f$ is a computable function from binary strings to natural numbers with
$f(x) \le K(x)$ for every binary string $x$, then there is a natural number $B$ with $f(x) \le B$
for every binary string $x$. -/
theorem exists_bound_of_computable_le_K {f : List Bool → ℕ} (hf : Computable f)
    (hle : ∀ x, f x ≤ K x) : ∃ B, ∀ x, f x ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_of_rePred_le_K (S := fun q ↦ q.2 = f q.1)
    (ComputablePred.to_re ⟨inferInstance,
      Primrec.eq.decide.to_comp.comp Computable.snd (hf.comp Computable.fst)⟩)
    fun q hq ↦ hq ▸ hle q.1
  exact ⟨B, fun x ↦ hB (x, f x) rfl⟩

/-- **Kolmogorov complexity is not lower semicomputable.** Let $K$ denote Kolmogorov complexity.
The set of pairs $(x, n)$ of a binary string $x$ and a natural number $n$ with $n \le K(x)$ is not
recursively enumerable (recognizable). -/
theorem not_rePred_le_K : ¬REPred fun q : List Bool × ℕ ↦ q.2 ≤ K q.1 := by
  intro h
  obtain ⟨B, hB⟩ := exists_bound_of_rePred_le_K h fun _ hq ↦ hq
  obtain ⟨x, -, hx⟩ := exists_incompressible (B + 1)
  have := hB (x, B + 1) hx
  omega

/-- **No recognizable set with arbitrarily long members consists of incompressible strings.**
Let $K$ denote Kolmogorov complexity and $|x|$ the length of a binary string $x$. There is no
recursively enumerable (recognizable) set $S$ of binary strings such that for every natural
number $n$ some $x \in S$ has $|x| \ge n$, and every $x \in S$ satisfies $|x| \le K(x)$. -/
theorem not_rePred_of_forall_incompressible {S : List Bool → Prop} (hS : REPred S)
    (hlong : ∀ n, ∃ x, S x ∧ n ≤ x.length) (hinc : ∀ x, S x → x.length ≤ K x) : False := by
  obtain ⟨B, hB⟩ := exists_bound_of_rePred_le_K (S := fun q ↦ S q.1 ∧ q.2 = q.1.length)
    (MetaMathlibExt.REPred.and (Partrec.comp (g := fun q : List Bool × ℕ ↦ q.1) hS
      Computable.fst)
      (ComputablePred.to_re ⟨inferInstance, (Primrec.eq.decide.comp Primrec.snd
        (Primrec.list_length.comp Primrec.fst)).to_comp⟩))
    fun q hq ↦ hq.2 ▸ hinc q.1 hq.1
  obtain ⟨x, hx, hlen⟩ := hlong (B + 1)
  have := hB (x, x.length) ⟨hx, rfl⟩
  omega

/-- **The incompressible strings are not recognizable.** Let $K$ denote Kolmogorov complexity
and $|x|$ the length of a binary string $x$. The set of incompressible binary strings, that is,
of binary strings $x$ with $|x| \le K(x)$, is not recursively enumerable (recognizable). -/
theorem not_rePred_incompressible : ¬REPred fun x : List Bool ↦ x.length ≤ K x := by
  intro h
  refine not_rePred_of_forall_incompressible h (fun n ↦ ?_) fun _ hx ↦ hx
  obtain ⟨x, hx₁, hx₂⟩ := exists_incompressible n
  exact ⟨x, by omega, by omega⟩

/-- **The incompressible strings are not decidable.** Let $K$ denote Kolmogorov complexity and
$|x|$ the length of a binary string $x$. The set of incompressible binary strings, that is, of
binary strings $x$ with $|x| \le K(x)$, is not decidable. -/
theorem not_computablePred_incompressible : ¬ComputablePred fun x : List Bool ↦ x.length ≤ K x :=
  fun h ↦ not_rePred_incompressible h.to_re

end Cslib.Kolmogorov

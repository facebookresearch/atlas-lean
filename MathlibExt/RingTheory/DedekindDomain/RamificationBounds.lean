/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section

/-!
# Bounds on ramification index, inertia degree, and number of primes above

This file ports ATLAS `NumberTheoryI` Corollary 5.36. In the book's AKLB
setting (`A` a Dedekind domain with fraction field `K`, `L / K` a finite
separable extension, `B` the integral closure of `A` in `L`), for each maximal
ideal `𝔭` of `A` the number `g_𝔭`
of primes of `B` above `𝔭`, and the ramification indices `e_𝔮` and residue
degrees `f_𝔮` of each `𝔮 ∣ 𝔭`, all lie in the
interval `[1, n]` where `n = [L : K]`.

The proofs combine the fundamental identity
`Ideal.sum_ramification_inertia_eq_finrank` (each summand `e_𝔮 * f_𝔮` is at
least `1`, and every `e_𝔮` and `f_𝔮` is at most its product `e_𝔮 * f_𝔮`)
with the positivity lemmas `Ideal.ramificationIdx_pos` and
`Ideal.inertiaDeg_pos`, and with `IsDedekindDomain.one_le_primesOver_ncard`
for the lower bound on `g_𝔭`. The statements are given first with
`n = Module.finrank R S`; the fraction-field form with `n = Module.finrank K L`
follows from `IsFractionRing.finrank_eq`.
-/

namespace Ideal

variable {R S : Type*} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]

/-- A single summand is at most the sum in the fundamental identity. -/
private theorem term_le_sum (p : Ideal R) [p.IsMaximal]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R * q.inertiaDeg R ≤
      ∑ r : p.primesOver S, r.1.ramificationIdx R * r.1.inertiaDeg R := by
  have hQ : (⟨q, inferInstance, inferInstance⟩ : p.primesOver S) ∈
      (Finset.univ : Finset (p.primesOver S)) := Finset.mem_univ _
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (p.primesOver S)))
    (f := fun r : p.primesOver S => r.1.ramificationIdx R * r.1.inertiaDeg R)
    (fun r _ => Nat.zero_le _) hQ
  exact h

/-- **Bounds on the ramification index.** Let $R$ and $S$ be Dedekind domains, with $S$ an
$R$-algebra that is finitely generated and torsion-free as an $R$-module, and let $n$ be the rank
of $S$ as an $R$-module. If $\mathfrak{p}$ is a maximal ideal of $R$ and $\mathfrak{q}$ is a prime
ideal of $S$ lying over $\mathfrak{p}$, then the ramification index $e_{\mathfrak{q}}$ of
$\mathfrak{q}$ over $\mathfrak{p}$ satisfies $1 \le e_{\mathfrak{q}} \le n$.

Source: ATLAS NumberTheoryI, Corollary 5.36 (the $e_{\mathfrak{q}}$ part). -/
theorem ramificationIdx_mem_Icc (p : Ideal R) [p.IsMaximal]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R ∈ Set.Icc 1 (Module.finrank R S) := by
  refine ⟨Ideal.ramificationIdx_pos R q, ?_⟩
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S]
  exact le_trans (Nat.le_mul_of_pos_right (q.ramificationIdx R)
    (Ideal.inertiaDeg_pos q R)) (term_le_sum p q)

/-- **Bounds on the inertia degree.** Let $R$ and $S$ be Dedekind domains, with $S$ an $R$-algebra
that is finitely generated and torsion-free as an $R$-module, and let $n$ be the rank of $S$ as an
$R$-module. If $\mathfrak{p}$ is a maximal ideal of $R$ and $\mathfrak{q}$ is a prime ideal of $S$
lying over $\mathfrak{p}$, then the inertia degree $f_{\mathfrak{q}}$ of $\mathfrak{q}$ over
$\mathfrak{p}$ satisfies $1 \le f_{\mathfrak{q}} \le n$.

Source: ATLAS NumberTheoryI, Corollary 5.36 (the $f_{\mathfrak{q}}$ part). -/
theorem inertiaDeg_mem_Icc (p : Ideal R) [p.IsMaximal]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.inertiaDeg R ∈ Set.Icc 1 (Module.finrank R S) := by
  refine ⟨Ideal.inertiaDeg_pos q R, ?_⟩
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S]
  exact le_trans (Nat.le_mul_of_pos_left (q.inertiaDeg R)
    (Ideal.ramificationIdx_pos R q)) (term_le_sum p q)

/-- **Bounds on the number of primes above a prime.** Let $R$ and $S$ be Dedekind domains, with $S$
an $R$-algebra that is finitely generated and torsion-free as an $R$-module, and let $n$ be the
rank of $S$ as an $R$-module. If $\mathfrak{p}$ is a maximal ideal of $R$, then the number
$g_{\mathfrak{p}}$ of prime ideals of $S$ lying over $\mathfrak{p}$ satisfies
$1 \le g_{\mathfrak{p}} \le n$.

Source: ATLAS NumberTheoryI, Corollary 5.36 (the $g_{\mathfrak{p}}$ part). -/
theorem ncard_primesOver_mem_Icc (p : Ideal R) [p.IsMaximal] :
    (p.primesOver S).ncard ∈ Set.Icc 1 (Module.finrank R S) := by
  refine ⟨IsDedekindDomain.one_le_primesOver_ncard p S, ?_⟩
  rw [← Ideal.sum_ramification_inertia_eq_finrank p S, ← Set.fintypeCard_eq_ncard,
    Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun r _ => ?_
  exact Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Ideal.ramificationIdx_pos R r.1).ne'
      (Ideal.inertiaDeg_pos r.1 R).ne')

/-- **Bounds on ramification, inertia and splitting.** Let $R$ and $S$ be Dedekind domains, with
$S$ an $R$-algebra that is finitely generated and torsion-free as an $R$-module, and let $n$ be the
rank of $S$ as an $R$-module. If $\mathfrak{p}$ is a maximal ideal of $R$ and $\mathfrak{q}$ is a
prime ideal of $S$ lying over $\mathfrak{p}$, then the ramification index $e_{\mathfrak{q}}$ and
the inertia degree $f_{\mathfrak{q}}$ of $\mathfrak{q}$ over $\mathfrak{p}$ and the number
$g_{\mathfrak{p}}$ of prime ideals of $S$ lying over $\mathfrak{p}$ all lie in the interval
$[1, n]$.

Source: ATLAS NumberTheoryI, Corollary 5.36. -/
theorem ramification_inertia_card_mem_Icc (p : Ideal R) [p.IsMaximal]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R ∈ Set.Icc 1 (Module.finrank R S) ∧
      q.inertiaDeg R ∈ Set.Icc 1 (Module.finrank R S) ∧
      (p.primesOver S).ncard ∈ Set.Icc 1 (Module.finrank R S) :=
  ⟨ramificationIdx_mem_Icc p q, inertiaDeg_mem_Icc p q, ncard_primesOver_mem_Icc p⟩

/-- **Bounds on ramification, inertia and splitting, fraction-field form.** Let $R$ and $S$ be
Dedekind domains, with $S$ an $R$-algebra that is finitely generated and torsion-free as an
$R$-module. Let $K$ be the fraction field of $R$ and $L$ the fraction field of $S$, with $L$ a
$K$-algebra compatible with the maps $R \to K \to L$ and $R \to S \to L$, and let $n = [L : K]$.
If $\mathfrak{p}$ is a maximal ideal of $R$ and $\mathfrak{q}$ is a prime ideal of $S$ lying over
$\mathfrak{p}$, then the ramification index $e_{\mathfrak{q}}$ and the inertia degree
$f_{\mathfrak{q}}$ of $\mathfrak{q}$ over $\mathfrak{p}$ and the number $g_{\mathfrak{p}}$ of prime
ideals of $S$ lying over $\mathfrak{p}$ all lie in the interval $[1, n]$.

Source: ATLAS NumberTheoryI, Corollary 5.36. -/
theorem ramification_inertia_card_mem_Icc_of_isFractionRing
    (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R ∈ Set.Icc 1 (Module.finrank K L) ∧
      q.inertiaDeg R ∈ Set.Icc 1 (Module.finrank K L) ∧
      (p.primesOver S).ncard ∈ Set.Icc 1 (Module.finrank K L) := by
  rw [IsFractionRing.finrank_eq R K S L]
  exact ramification_inertia_card_mem_Icc p q

end Ideal

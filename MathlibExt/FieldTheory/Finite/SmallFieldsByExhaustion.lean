/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.TracesOfIrreducibleQuadratics
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# $U_q + U_q = \mathbb{F}_q$ for $q \in \{13, 16, 17, 19\}$, by exhaustion

Let $U_q$ be the set of $s \in \mathbb{F}_q$ such that $x^2 - sx + 1$ is irreducible in
$\mathbb{F}_q[x]$ (`FiniteField.tracesOfIrreducibleQuadratics`). For every finite field $K$ with
$13$, $16$, $17$ or $19$ elements, every element of $K$ is a sum $s + s'$ with $s, s' \in U_K$.
This is the exhaustion step in the proof of Lemma 2.3 of B. Poonen, "Characterizing integers
among rational numbers with a universal-existential formula", Amer. J. Math. 131 (2009),
675–682.

The results:

* `FiniteField.tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen`,
  `FiniteField.tracesOfIrreducibleQuadratics_add_self_of_card_eq_sixteen`,
  `FiniteField.tracesOfIrreducibleQuadratics_add_self_of_card_eq_seventeen` and
  `FiniteField.tracesOfIrreducibleQuadratics_add_self_of_card_eq_nineteen`: $U_K + U_K = K$ for a
  finite field $K$ with $13$, $16$, $17$, respectively $19$ elements;
* `FiniteField.tracesOfIrreducibleQuadratics_add_self_of_eleven_lt_card_of_card_lt_twentyThree`:
  $U_K + U_K = K$ for every finite field $K$ with $11 < \# K < 23$.

## Implementation notes

A finite field with $q$ elements is isomorphic to every other one (`FiniteField.ringEquivOfCardEq`),
and $U_q$ is preserved by ring isomorphisms
(`FiniteField.map_mem_tracesOfIrreducibleQuadratics_iff`), so it suffices to check one model of
$\mathbb{F}_q$. For $q$ prime the model is `ZMod q`. For $q = 16$ the model is a private type: the
integers $0, \dots, 15$ read as polynomials of degree less than $4$ over $\mathbb{F}_2$ (bit $i$ is
the coefficient of $t^i$), with addition the bitwise exclusive or and multiplication modulo
$t^4 + t + 1$. Its commutative ring axioms and the absence of zero divisors are checked by
evaluation in the kernel, and `Fintype.fieldOfDomain` makes it a field. In each model an explicit
finite set of elements of $U_q$ is checked by evaluation in the kernel to satisfy the root
criterion `FiniteField.mem_tracesOfIrreducibleQuadratics_iff` and to have every element of the
field as a sum of two of its elements.
-/

set_option autoImplicit false

@[expose] public section

open scoped Pointwise

namespace FiniteField

/-- A finite set of elements of $U_K$ whose pairwise sums cover $K$ gives $U_K + U_K = K$. -/
private theorem tracesOfIrreducibleQuadratics_add_self_of_finset {K : Type*} [Field K]
    (S : Finset K) (hS : ∀ s ∈ S, ∀ r : K, r ^ 2 - s * r + 1 ≠ 0)
    (hcover : ∀ a : K, ∃ s ∈ S, ∃ s' ∈ S, s + s' = a) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ := by
  refine Set.eq_univ_of_forall fun a => ?_
  obtain ⟨s, hs, s', hs', rfl⟩ := hcover a
  exact Set.add_mem_add (mem_tracesOfIrreducibleQuadratics_iff.2 (hS s hs))
    (mem_tracesOfIrreducibleQuadratics_iff.2 (hS s' hs'))

/-- $U_K + U_K = K$ transports along a ring isomorphism $K \to K'$. -/
private theorem tracesOfIrreducibleQuadratics_add_self_of_ringEquiv {K K' : Type*} [Field K]
    [Field K'] (e : K ≃+* K')
    (h : tracesOfIrreducibleQuadratics K' + tracesOfIrreducibleQuadratics K' = Set.univ) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ := by
  refine Set.eq_univ_of_forall fun a => ?_
  obtain ⟨s, hs, s', hs', hss'⟩ := Set.mem_add.1 (h ▸ Set.mem_univ (e a))
  refine ⟨e.symm s, ?_, e.symm s', ?_, ?_⟩
  · rw [← map_mem_tracesOfIrreducibleQuadratics_iff e, e.apply_symm_apply]
    exact hs
  · rw [← map_mem_tracesOfIrreducibleQuadratics_iff e, e.apply_symm_apply]
    exact hs'
  · change e.symm s + e.symm s' = a
    rw [← map_add, hss', e.symm_apply_apply]

/-! ### The prime fields -/

private instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

private instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

private theorem zmod13_mem : ∀ s ∈ ({3, 5, 6, 7, 8, 10} : Finset (ZMod 13)),
    ∀ r : ZMod 13, r ^ 2 - s * r + 1 ≠ 0 := by
  decide +kernel

private theorem zmod13_cover : ∀ a : ZMod 13,
    ∃ s ∈ ({3, 5, 6, 7, 8, 10} : Finset (ZMod 13)),
      ∃ s' ∈ ({3, 5, 6, 7, 8, 10} : Finset (ZMod 13)), s + s' = a := by
  decide +kernel

private theorem zmod17_mem : ∀ s ∈ ({1, 3, 4, 7, 10, 13, 14, 16} : Finset (ZMod 17)),
    ∀ r : ZMod 17, r ^ 2 - s * r + 1 ≠ 0 := by
  decide +kernel

private theorem zmod17_cover : ∀ a : ZMod 17,
    ∃ s ∈ ({1, 3, 4, 7, 10, 13, 14, 16} : Finset (ZMod 17)),
      ∃ s' ∈ ({1, 3, 4, 7, 10, 13, 14, 16} : Finset (ZMod 17)), s + s' = a := by
  decide +kernel

private theorem zmod19_mem : ∀ s ∈ ({0, 4, 5, 6, 8, 11, 13, 14, 15} : Finset (ZMod 19)),
    ∀ r : ZMod 19, r ^ 2 - s * r + 1 ≠ 0 := by
  decide +kernel

private theorem zmod19_cover : ∀ a : ZMod 19,
    ∃ s ∈ ({0, 4, 5, 6, 8, 11, 13, 14, 15} : Finset (ZMod 19)),
      ∃ s' ∈ ({0, 4, 5, 6, 8, 11, 13, 14, 15} : Finset (ZMod 19)), s + s' = a := by
  decide +kernel

/-! ### A model of the field with $16$ elements -/

/-- A model of $\mathbb{F}_{16} = \mathbb{F}_2[t]/(t^4 + t + 1)$: the integer $n < 16$ stands for
the polynomial whose coefficient of $t^i$ is bit $i$ of $n$. -/
private def F16 : Type := Fin 16

private instance : DecidableEq F16 := inferInstanceAs (DecidableEq (Fin 16))

private instance : Fintype F16 := inferInstanceAs (Fintype (Fin 16))

/-- The element of `F16` with code `n % 16`. -/
private def F16.ofNat (n : ℕ) : F16 := (⟨n % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16)

/-- The code of an element of `F16`. -/
private def F16.val (a : F16) : ℕ := Fin.val (n := 16) a

/-- Carry-less product of `a < 16` and `b < 16`, reduced modulo $t^4 + t + 1$ (bit pattern
`10011`): the bits of degree $6$, $5$ and $4$ are cleared by subtracting the shifts
`1001100`, `100110` and `10011`. -/
private def F16.mulNat (a b : ℕ) : ℕ :=
  let p := (if b &&& 1 = 0 then 0 else a) ^^^ (if b &&& 2 = 0 then 0 else a <<< 1) ^^^
    (if b &&& 4 = 0 then 0 else a <<< 2) ^^^ (if b &&& 8 = 0 then 0 else a <<< 3)
  let p := if p &&& 64 = 0 then p else p ^^^ 76
  let p := if p &&& 32 = 0 then p else p ^^^ 38
  if p &&& 16 = 0 then p else p ^^^ 19

private instance : Zero F16 := ⟨F16.ofNat 0⟩

private instance : One F16 := ⟨F16.ofNat 1⟩

private instance : Add F16 := ⟨fun a b => F16.ofNat (a.val ^^^ b.val)⟩

private instance : Neg F16 := ⟨fun a => a⟩

private instance : Mul F16 := ⟨fun a b => F16.ofNat (F16.mulNat a.val b.val)⟩

private theorem F16.add_assoc' : ∀ a b c : F16, a + b + c = a + (b + c) := by
  decide +kernel

private theorem F16.zero_add' : ∀ a : F16, 0 + a = a := by
  decide +kernel

private theorem F16.add_zero' : ∀ a : F16, a + 0 = a := by
  decide +kernel

private theorem F16.add_comm' : ∀ a b : F16, a + b = b + a := by
  decide +kernel

private theorem F16.neg_add_cancel' : ∀ a : F16, -a + a = 0 := by
  decide +kernel

private theorem F16.mul_assoc' : ∀ a b c : F16, a * b * c = a * (b * c) := by
  decide +kernel

private theorem F16.one_mul' : ∀ a : F16, 1 * a = a := by
  decide +kernel

private theorem F16.mul_one' : ∀ a : F16, a * 1 = a := by
  decide +kernel

private theorem F16.zero_mul' : ∀ a : F16, 0 * a = 0 := by
  decide +kernel

private theorem F16.mul_zero' : ∀ a : F16, a * 0 = 0 := by
  decide +kernel

private theorem F16.mul_comm' : ∀ a b : F16, a * b = b * a := by
  decide +kernel

private theorem F16.left_distrib' : ∀ a b c : F16, a * (b + c) = a * b + a * c := by
  decide +kernel

private theorem F16.right_distrib' : ∀ a b c : F16, (a + b) * c = a * c + b * c := by
  decide +kernel

private theorem F16.eq_zero_or_eq_zero_of_mul_eq_zero' :
    ∀ a b : F16, a * b = 0 → a = 0 ∨ b = 0 := by
  decide +kernel

private instance : CommRing F16 where
  add_assoc := F16.add_assoc'
  zero_add := F16.zero_add'
  add_zero := F16.add_zero'
  add_comm := F16.add_comm'
  neg_add_cancel := F16.neg_add_cancel'
  mul_assoc := F16.mul_assoc'
  one_mul := F16.one_mul'
  mul_one := F16.mul_one'
  zero_mul := F16.zero_mul'
  mul_zero := F16.mul_zero'
  mul_comm := F16.mul_comm'
  left_distrib := F16.left_distrib'
  right_distrib := F16.right_distrib'
  nsmul := nsmulRec
  zsmul := zsmulRec

private instance : Nontrivial F16 := ⟨⟨0, 1, by decide⟩⟩

private instance : NoZeroDivisors F16 :=
  ⟨fun {a b} => F16.eq_zero_or_eq_zero_of_mul_eq_zero' a b⟩

private instance : IsDomain F16 := NoZeroDivisors.to_isDomain F16

private noncomputable instance : Field F16 := Fintype.fieldOfDomain F16

private theorem F16.card : Fintype.card F16 = 16 := Fintype.card_fin 16

/-- The elements of $U_{16}$ in the model `F16`, by their codes. -/
private def F16.U : Finset F16 :=
  {F16.ofNat 2, F16.ofNat 3, F16.ofNat 4, F16.ofNat 5, F16.ofNat 8, F16.ofNat 10, F16.ofNat 12,
    F16.ofNat 15}

private theorem F16.U_mem : ∀ s ∈ F16.U, ∀ r : F16, r ^ 2 - s * r + 1 ≠ 0 := by
  decide +kernel

private theorem F16.U_cover : ∀ a : F16, ∃ s ∈ F16.U, ∃ s' ∈ F16.U, s + s' = a := by
  decide +kernel

/-! ### The exhaustion -/

variable {K : Type*} [Field K] [Fintype K]

/-- **$U_{13} + U_{13} = \mathbb{F}_{13}$.** For every finite field $K$ with $13$ elements, every
element of $K$ is $s + s'$ for some $s, s' \in K$ such that $x^2 - sx + 1$ and $x^2 - s'x + 1$ are
irreducible in $K[x]$. The proof checks in $\mathbb{Z}/13$ that $3, 5, 6, 7, 8, 10 \in U_{13}$ and
that their pairwise sums cover $\mathbb{Z}/13$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, last sentence, p. 3 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "If $11 < q < 23$ we check
$U_q + U_q = \mathbb{F}_q$ by exhaustion." -/
theorem tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen (hK : Fintype.card K = 13) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_ringEquiv
    (ringEquivOfCardEq (K' := ZMod 13) (by rw [hK, ZMod.card]))
    (tracesOfIrreducibleQuadratics_add_self_of_finset _ zmod13_mem zmod13_cover)

/-- **$U_{16} + U_{16} = \mathbb{F}_{16}$.** For every finite field $K$ with $16$ elements, every
element of $K$ is $s + s'$ for some $s, s' \in K$ such that $x^2 - sx + 1$ and $x^2 - s'x + 1$ are
irreducible in $K[x]$. The proof checks in $\mathbb{F}_2[t]/(t^4 + t + 1)$ that $t$, $t + 1$,
$t^2$, $t^2 + 1$, $t^3$, $t^3 + t$, $t^3 + t^2$ and $t^3 + t^2 + t + 1$ lie in $U_{16}$ and that
their pairwise sums cover the field.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, last sentence, p. 3 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "If $11 < q < 23$ we check
$U_q + U_q = \mathbb{F}_q$ by exhaustion." -/
theorem tracesOfIrreducibleQuadratics_add_self_of_card_eq_sixteen (hK : Fintype.card K = 16) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_ringEquiv
    (ringEquivOfCardEq (K' := F16) (by rw [hK, F16.card]))
    (tracesOfIrreducibleQuadratics_add_self_of_finset _ F16.U_mem F16.U_cover)

/-- **$U_{17} + U_{17} = \mathbb{F}_{17}$.** For every finite field $K$ with $17$ elements, every
element of $K$ is $s + s'$ for some $s, s' \in K$ such that $x^2 - sx + 1$ and $x^2 - s'x + 1$ are
irreducible in $K[x]$. The proof checks in $\mathbb{Z}/17$ that
$1, 3, 4, 7, 10, 13, 14, 16 \in U_{17}$ and that their pairwise sums cover $\mathbb{Z}/17$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, last sentence, p. 3 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "If $11 < q < 23$ we check
$U_q + U_q = \mathbb{F}_q$ by exhaustion." -/
theorem tracesOfIrreducibleQuadratics_add_self_of_card_eq_seventeen (hK : Fintype.card K = 17) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_ringEquiv
    (ringEquivOfCardEq (K' := ZMod 17) (by rw [hK, ZMod.card]))
    (tracesOfIrreducibleQuadratics_add_self_of_finset _ zmod17_mem zmod17_cover)

/-- **$U_{19} + U_{19} = \mathbb{F}_{19}$.** For every finite field $K$ with $19$ elements, every
element of $K$ is $s + s'$ for some $s, s' \in K$ such that $x^2 - sx + 1$ and $x^2 - s'x + 1$ are
irreducible in $K[x]$. The proof checks in $\mathbb{Z}/19$ that
$0, 4, 5, 6, 8, 11, 13, 14, 15 \in U_{19}$ and that their pairwise sums cover $\mathbb{Z}/19$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, last sentence, p. 3 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "If $11 < q < 23$ we check
$U_q + U_q = \mathbb{F}_q$ by exhaustion." -/
theorem tracesOfIrreducibleQuadratics_add_self_of_card_eq_nineteen (hK : Fintype.card K = 19) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ :=
  tracesOfIrreducibleQuadratics_add_self_of_ringEquiv
    (ringEquivOfCardEq (K' := ZMod 19) (by rw [hK, ZMod.card]))
    (tracesOfIrreducibleQuadratics_add_self_of_finset _ zmod19_mem zmod19_cover)

/-- **$U_q + U_q = \mathbb{F}_q$ for $11 < q < 23$.** For every finite field $K$ with $q$ elements,
where $11 < q < 23$, every element of $K$ is $s + s'$ for some $s, s' \in K$ such that
$x^2 - sx + 1$ and $x^2 - s'x + 1$ are irreducible in $K[x]$. The prime powers $q$ with
$11 < q < 23$ are $13$, $16$, $17$ and $19$; the other $q$ in this range are not cardinalities of
finite fields (`FiniteField.isPrimePow_card`).

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, proof of Lemma 2.3, last sentence, p. 3 of the
author's version with the corrections of April 15, 2019
(<https://math.mit.edu/~poonen/papers/ae.pdf>): "If $11 < q < 23$ we check
$U_q + U_q = \mathbb{F}_q$ by exhaustion." -/
theorem tracesOfIrreducibleQuadratics_add_self_of_eleven_lt_card_of_card_lt_twentyThree
    (h₁ : 11 < Fintype.card K) (h₂ : Fintype.card K < 23) :
    tracesOfIrreducibleQuadratics K + tracesOfIrreducibleQuadratics K = Set.univ := by
  have hpp := FiniteField.isPrimePow_card K
  obtain h | h | h | h : Fintype.card K = 13 ∨ Fintype.card K = 16 ∨ Fintype.card K = 17 ∨
      Fintype.card K = 19 := by
    generalize Fintype.card K = q at hpp h₁ h₂ ⊢
    interval_cases q <;> first | decide | exact absurd hpp (by decide +kernel)
  · exact tracesOfIrreducibleQuadratics_add_self_of_card_eq_thirteen h
  · exact tracesOfIrreducibleQuadratics_add_self_of_card_eq_sixteen h
  · exact tracesOfIrreducibleQuadratics_add_self_of_card_eq_seventeen h
  · exact tracesOfIrreducibleQuadratics_add_self_of_card_eq_nineteen h

end FiniteField

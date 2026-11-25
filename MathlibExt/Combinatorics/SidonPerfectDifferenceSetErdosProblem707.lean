/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import MathlibExt.Combinatorics.Additive.Sidon
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Forbidden Sidon subsets of perfect difference sets

The Sidon set `{1, 2, 4, 8}` has no extension to a perfect difference set modulo
`p ^ 2 + p + 1` for any prime `p`. The proof follows the involution argument of
Alexeev and Mixon in Section 3 of <https://arxiv.org/html/2510.19804>.

The Sidon set `{1, 2, 4, 8, 13}` has no extension to a perfect difference set modulo
`m ^ 2 + m + 1` for any `m ≥ 1`, which refutes the weak form of the problem. For `m ≤ 2` two of
its elements share a residue. For odd `m ≥ 3` an extension has an even number of elements and is
excluded as above. For even `m ≥ 4` it has an odd number of elements; counting the fixed points of
the same involution then gives Baer's collinearity of absolute points, as in Alexeev and Mixon's
proof of their Theorem 9 (Section 5).

Erdős Problem 707: let `A ⊂ ℕ` be a finite Sidon set. Is there some set `B` with `A ⊆ B` which is a
perfect difference set modulo `p² + p + 1` for some prime `p`?

Source: T. F. Bloom, Erdős Problems, Problem #707, https://www.erdosproblems.com/707 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006987 (`EP-707`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon is MathlibExt's `Set.IsSidon` (repeated summands included). `B ⊆ ℕ` is a perfect difference
set modulo `v` when every nonzero residue is `a - b (mod v)` for exactly one ordered pair `(a, b) ∈
B × B`; uniqueness forces the elements of `B` to be distinct modulo `v`. A second formulation is
Erdős's weaker form with modulus `m² + m + 1`, `m ≥ 1` (every finite perfect difference set with at
least two elements has such a modulus); `m = 0` (modulus `1`) is excluded since every set is
vacuously a perfect difference set modulo `1`. Compared with the formal-conjectures statement
`ErdosProblems/707.lean` (formal-conjectures uses any positive modulus in its main statement; no
code imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707Wanted

/-- **Perfect difference sets modulo $v$.** A set $B \subseteq \mathbb{N}$ is a perfect difference
set modulo a natural number $v$ when every nonzero residue $x$ modulo $v$ satisfies
$x \equiv a - b \pmod{v}$ for exactly one ordered pair $(a, b)$ of elements of $B$. -/
def IsPerfectDifferenceSetMod (B : Set ℕ) (v : ℕ) : Prop :=
  ∀ x : ZMod v, x ≠ 0 → ∃! ab : ℕ × ℕ, ab.1 ∈ B ∧ ab.2 ∈ B ∧ (ab.1 : ZMod v) - ab.2 = x

/-- **Erdős Problem 707.** The proposition that for every finite Sidon set $A \subseteq \mathbb{N}$
there are a prime $p$ and a set $B \subseteq \mathbb{N}$ with $A \subseteq B$ such that $B$ is a
perfect difference set modulo $p^2 + p + 1$. -/
def sidonExtendsToPrimePerfectDifferenceSet : Prop :=
  ∀ A : Set ℕ, A.Finite → A.IsSidon →
    ∃ p : ℕ, p.Prime ∧ ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSetMod B (p ^ 2 + p + 1)

/-- **Erdős Problem 707, weak form.** The proposition that for every finite Sidon set
$A \subseteq \mathbb{N}$ there are a natural number $m \ge 1$ and a set $B \subseteq \mathbb{N}$
with $A \subseteq B$ such that $B$ is a perfect difference set modulo $m^2 + m + 1$.

This weakens Erdős Problem 707 by allowing any $m \ge 1$ in place of a prime $p$. -/
def sidonExtendsToPerfectDifferenceSet : Prop :=
  ∀ A : Set ℕ, A.Finite → A.IsSidon →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ B : Set ℕ, A ⊆ B ∧ IsPerfectDifferenceSetMod B (m ^ 2 + m + 1)

/-- The unique difference representations on the finite set of residues of an extension. -/
private def UniqueDifferences {v : ℕ} (D : Finset (ZMod v)) : Prop :=
  ∀ r : ZMod v, r ≠ 0 → ∃! ab : D × D, (ab.1 : ZMod v) - ab.2 = r

private lemma uniqueDifferences_of_image {B : Set ℕ} {v : ℕ} {D : Finset (ZMod v)}
    (hB : IsPerfectDifferenceSetMod B v)
    (hD : ∀ z, z ∈ D ↔ ∃ b ∈ B, (b : ZMod v) = z) : UniqueDifferences D := by
  intro r hr
  obtain ⟨⟨a, b⟩, ⟨ha, hb, hab⟩, uniq⟩ := hB r hr
  refine ⟨(⟨a, (hD _).2 ⟨a, ha, rfl⟩⟩, ⟨b, (hD _).2 ⟨b, hb, rfl⟩⟩), hab, ?_⟩
  rintro ⟨⟨_, hc⟩, ⟨_, hd⟩⟩ hcd
  obtain ⟨c, hc', rfl⟩ := (hD _).1 hc
  obtain ⟨d, hd', rfl⟩ := (hD _).1 hd
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (uniq (c, d) ⟨hc', hd', hcd⟩)
  rfl

private lemma pair_eq {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    {a b c d : D} (hab : a ≠ b)
    (heq : (a : ZMod v) - b = (c : ZMod v) - d) : (a, b) = (c, d) :=
  (hD _ (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr hab))).unique rfl heq.symm

/-- Count ordered pairs off the diagonal by their differences. -/
private lemma card_of_uniqueDifferences {p : ℕ} {D : Finset (ZMod (p ^ 2 + p + 1))}
    (hD : UniqueDifferences D) (hp : 0 < p) : D.card = p + 1 := by
  classical
  let v := p ^ 2 + p + 1
  have hcard : (Finset.univ : Finset D).offDiag.card =
      (Finset.univ.erase (0 : ZMod v)).card := by
    apply Finset.card_bij (fun ab _ => (ab.1 : ZMod v) - ab.2)
    · intro ab hab
      simpa using sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr (Finset.mem_offDiag.mp hab).2.2)
    · intro ab hab cd _ heq
      exact pair_eq hD (Finset.mem_offDiag.mp hab).2.2 heq
    · intro r hr
      have hr0 : r ≠ 0 := (Finset.mem_erase.mp hr).1
      obtain ⟨⟨a, b⟩, hab⟩ := (hD r hr0).exists
      refine ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩, hab⟩
      change a ≠ b
      rintro rfl
      exact hr0 (by simpa using hab.symm)
  have count : D.card * D.card - D.card = p ^ 2 + p := by
    simpa [Finset.offDiag_card, ZMod.card, v] using hcard
  have hle : D.card ≤ D.card * D.card := Nat.le_mul_self _
  have h := Nat.sub_add_cancel hle
  rw [count] at h
  have hprod : ((D.card : ℤ) + p) * (D.card - (p : ℤ) - 1) = 0 := by
    have heq : (D.card : ℤ) * D.card = (p : ℤ) ^ 2 + p + D.card := by exact_mod_cast h.symm
    linarith only [heq]
  rcases mul_eq_zero.mp hprod with hz | hz <;> omega

/-- For a residue outside the set, the representation of `a - b` as `c - d` pairs
`b` with `c`. A fixed point of this involution has a companion when the set has even size. -/
private lemma second_fixed_point {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    (heven : 2 ∣ D.card) (a : ZMod v) (ha : a ∉ D) (x u : D)
    (hx : a - x = (x : ZMod v) - u) :
    ∃ b d : D, b ≠ x ∧ 2 * (b : ZMod v) = a + d := by
  classical
  have hn (b : D) : a - b ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ b.property)
  choose pair hpair huniq using fun b : D => hD (a - b) (hn b)
  let f (b : D) := (pair b).1
  have hflip (b : D) : (b, (pair b).2) = pair (f b) := by
    apply huniq
    change (b : ZMod v) - (pair b).2 = a - (pair b).1
    linear_combination hpair b
  have hinv : Function.Involutive f := fun b => (congrArg Prod.fst (hflip b)).symm
  let σ := hinv.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    apply Equiv.ext
    intro b
    simpa only [pow_one, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, σ,
      Function.Involutive.coe_toPerm] using hinv b
  have hfix : σ x = x := (congrArg Prod.fst (huniq x (x, u) hx.symm)).symm
  obtain ⟨b, hb, hbx⟩ := Equiv.Perm.exists_fixed_point_of_prime' (p := 2)
    (by simpa using heven) hσ hfix
  refine ⟨b, (pair b).2, hbx, ?_⟩
  change (pair b).1 = b at hb
  have heq : ((pair b).1 : ZMod v) - (pair b).2 = a - b := hpair b
  rw [hb] at heq
  linear_combination heq

/-- Taking `a = 2x - u` gives a difference between two doubled elements for each `x`. -/
private lemma exists_partner {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    (heven : 2 ∣ D.card) (u x : D) :
    ∃ b d : D, 2 * (b : ZMod v) = 2 * x - u + d ∧ (b = x → x = u) := by
  by_cases hxu : x = u
  · exact ⟨x, u, by ring, fun _ => hxu⟩
  have hout : 2 * (x : ZMod v) - u ∉ D := by
    intro h
    let y : D := ⟨_, h⟩
    have heq : (x : ZMod v) - u = (y : ZMod v) - x := by dsimp [y]; ring
    exact hxu (congrArg Prod.snd (pair_eq hD hxu heq)).symm
  obtain ⟨b, d, hbx, heq⟩ := second_fixed_point hD heven _ hout x u (by ring)
  exact ⟨b, d, heq, fun h => (hbx h).elim⟩

/-- Cancel a factor of two even when the odd modulus is composite. -/
private lemma cancel_two {v : ℕ} (hv : Odd v) {a b : ZMod v} (h : 2 * a = 2 * b) :
    a = b := by
  apply sub_eq_zero.mp
  apply (ZMod.add_self_eq_zero_iff_eq_zero hv).mp
  linear_combination h

/-- Distinct naturals below the modulus have distinct residues. -/
private lemma natCast_ne_of_lt {v : ℕ} (m n : ℕ) (hm : m < v) (hn : n < v) (hmn : m ≠ n) :
    (m : ZMod v) ≠ (n : ZMod v) := by
  intro h
  apply hmn
  simpa only [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] using congrArg ZMod.val h

private lemma no_extension_odd {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    (heven : 2 ∣ D.card) (hv : Odd v) (hlt : 8 < v)
    (h1 : 1 ∈ D) (h2 : 2 ∈ D) (h4 : 4 ∈ D) (h8 : 8 ∈ D) : False := by
  classical
  let u : D := ⟨2, h2⟩
  choose b d hbd hspecial using exists_partner hD heven u
  have hinj : Function.Injective d := by
    intro x y heq
    by_contra hxy
    have hdiff : (x : ZMod v) - y = (b x : ZMod v) - b y := by
      apply cancel_two hv
      have he := hbd x
      rw [heq] at he
      linear_combination hbd y - he
    have hp := pair_eq hD hxy hdiff
    have hx := hspecial x (congrArg Prod.fst hp).symm
    have hy := hspecial y (congrArg Prod.snd hp).symm
    exact hxy (hx.trans hy.symm)
  -- A prescribed difference between doubled elements forces the preimage of `w` under `d`.
  have forced (y z w : D) (hyz : y ≠ z) (hw : (w : ZMod v) - u = 2 * (y - (z : ZMod v))) :
      d z = w := by
    obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj w
    have he := hbd x
    rw [hx] at he
    have hdif : (y : ZMod v) - z = (b x : ZMod v) - x := by
      apply cancel_two hv
      linear_combination -hw - he
    have hzx : z = x := congrArg Prod.snd (pair_eq hD hyz hdif)
    exact hzx ▸ hx
  have distinct := natCast_ne_of_lt (v := v)
  let one : D := ⟨1, h1⟩
  let four : D := ⟨4, h4⟩
  let eight : D := ⟨8, h8⟩
  have hu1 : u ≠ one := fun e => distinct 2 1 (by omega) (by omega) (by decide)
    (by simpa [u, one] using congrArg Subtype.val e)
  have h41 : four ≠ one := fun e => distinct 4 1 (by omega) (by omega) (by decide)
    (by simpa [four, one] using congrArg Subtype.val e)
  have hfour := forced u one four hu1 (by change 4 - 2 = 2 * (2 - 1 : ZMod v); ring)
  have height := forced four one eight h41 (by change 8 - 2 = 2 * (4 - 1 : ZMod v); ring)
  apply distinct 4 8 (by omega) hlt (by decide)
  simpa [four, eight] using congrArg Subtype.val (hfour.symm.trans height)

/--
**Erdős Problem 707 is false.** It is not the case that every finite Sidon set
$A \subseteq \mathbb{N}$ is contained in a perfect difference set modulo $p^2 + p + 1$ for some
prime $p$: there is a finite Sidon set $A \subseteq \mathbb{N}$ such that for every prime $p$, no
set $B \subseteq \mathbb{N}$ with $A \subseteq B$ is a perfect difference set modulo
$p^2 + p + 1$. Here $A$ is Sidon when $w + x = y + z$ with $w, x, y, z \in A$ forces
$\{w, x\} = \{y, z\}$, and $B$ is a perfect difference set modulo $v$ when every nonzero residue
$r$ modulo $v$ satisfies $r \equiv a - b \pmod{v}$ for exactly one ordered pair $(a, b)$ of
elements of $B$.

Alexeev and Mixon proved that the Sidon set $\{1, 2, 4, 8\}$ is such a set (their proof is
formalized in Lean); erdosproblems.com/707 lists the problem as disproved.

Source: T. F. Bloom, Erdős Problems, Problem
#707, https://www.erdosproblems.com/707 (status DISPROVED (LEAN)); resolution: B. Alexeev and D. G.
Mixon, Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof,
arXiv:2510.19804 (2025); M. Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079-1090,
abstract of arXiv:2510.19804: {1, 2, 4, 8, 13} is a finite Sidon set contained in no finite perfect
difference set; erdosproblems.com/707: {1, 2, 4, 8} cannot be extended to a perfect difference set
modulo p² + p + 1 for any prime p, and Hall's {1, 3, 9, 10, 13} cannot be extended to any perfect
difference set, https://arxiv.org/abs/2510.19804.
-/
public theorem sidonExtendsToPrimePerfectDifferenceSet_refuted :
    ¬ sidonExtendsToPrimePerfectDifferenceSet := by
  classical
  let A : Set ℕ := {1, 2, 4, 8}
  have hfin : A.Finite := by simp [A]
  have hsidon : A.IsSidon := by
    intro a ha b hb c hc d hd
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
    omega
  intro hext
  obtain ⟨p, hp, B, hAB, hB⟩ := hext A hfin hsidon
  have h1 : 1 ∈ B := hAB (by simp [A])
  have h2 : 2 ∈ B := hAB (by simp [A])
  have h8 : 8 ∈ B := hAB (by simp [A])
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have collision : (2, 1) = (2, 8) :=
      (hB 1 (by decide)).unique ⟨h2, h1, by decide⟩ ⟨h2, h8, by decide⟩
    contradiction
  · let v := p ^ 2 + p + 1
    let D := Finset.univ.filter (fun z : ZMod v => ∃ b ∈ B, (b : ZMod v) = z)
    have hmem (z : ZMod v) : z ∈ D ↔ ∃ b ∈ B, (b : ZMod v) = z := by simp [D]
    have hD := uniqueDifferences_of_image hB hmem
    have hcard := card_of_uniqueDifferences hD hp.pos
    have mem {n : ℕ} (hn : n ∈ A) : (n : ZMod v) ∈ D := (hmem _).2 ⟨n, hAB hn, rfl⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      have := Nat.odd_iff.mp hodd
      omega
    apply no_extension_odd hD
    · rw [hcard]
      exact even_iff_two_dvd.mp hodd.add_one
    · exact (hodd.pow.add_odd hodd).add_one
    · nlinarith [Nat.mul_self_le_mul_self hp3]
    · simpa using mem (n := 1) (by simp [A])
    · simpa using mem (n := 2) (by simp [A])
    · simpa using mem (n := 4) (by simp [A])
    · simpa using mem (n := 8) (by simp [A])

/-! ### Extensions of odd size

For the weak form, an extension may have an odd number `m + 1` of elements. The residues modulo
`v` and the translates of the set form a projective plane, and `x ↦ D - x` is a polarity whose
absolute points are the residues `x` with `2 * x` in the set (Alexeev and Mixon, Section 5,
Lemma 19). The lemmas below are the parts of Baer's results on absolute points that their proof
of Theorem 9 uses for planes of even order `m` (Propositions 20, 21, 24 and 25), stated directly
in terms of the set. -/

/-- In a set of odd size, each residue `a` is `2 * b - d` for an odd number of elements `b` of
the set, with `d` in the set: every line carries an odd number of absolute points. For `a` outside
the set these `b` are the fixed points of the involution of `second_fixed_point`; for `a` in the
set, `b = a` is the only one. -/
private lemma odd_card_midpoints {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    (hodd : ¬ 2 ∣ D.card) (a : ZMod v) :
    ¬ 2 ∣ Fintype.card {b : D // 2 * (b : ZMod v) - a ∈ D} := by
  by_cases ha : a ∈ D
  · have hone : Fintype.card {b : D // 2 * (b : ZMod v) - a ∈ D} = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨⟨a, ha⟩, by simpa [two_mul] using ha⟩, ?_⟩
      rintro ⟨b, hb⟩
      have hba : b = ⟨a, ha⟩ := by
        by_contra hba
        have hp := pair_eq hD hba (c := ⟨_, hb⟩) (d := b)
          (by change (b : ZMod v) - a = 2 * (b : ZMod v) - a - b; ring)
        exact hba (congrArg Prod.snd hp).symm
      exact Subtype.ext hba
    omega
  · have hn (b : D) : a - b ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ b.property)
    choose pair hpair huniq using fun b : D => hD (a - b) (hn b)
    let f (b : D) := (pair b).1
    have hflip (b : D) : (b, (pair b).2) = pair (f b) := by
      apply huniq
      change (b : ZMod v) - (pair b).2 = a - (pair b).1
      linear_combination hpair b
    have hinv : Function.Involutive f := fun b => (congrArg Prod.fst (hflip b)).symm
    have hfix (b : D) : b ∈ Function.fixedPoints f ↔ 2 * (b : ZMod v) - a ∈ D := by
      constructor
      · intro hb
        have hb' : (pair b).1 = b := hb
        have h : ((pair b).1 : ZMod v) - (pair b).2 = a - b := hpair b
        rw [hb'] at h
        have he : 2 * (b : ZMod v) - a = (pair b).2 := by linear_combination h
        rw [he]
        exact (pair b).2.property
      · intro hb
        exact (congrArg Prod.fst (huniq b (b, ⟨_, hb⟩) (by dsimp only; ring))).symm
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1)
      (Function.involutive_iff_iter_2_eq_id.mp hinv)
    rw [Fintype.card_congr (Equiv.subtypeEquivRight hfix), Fintype.card_coe] at hmod
    unfold Nat.ModEq at hmod
    omega

/-- Baer's collinearity of absolute points, on the line `D` itself: if the set has odd size and
contains `2 * y` and `2 * z` for two of its elements `y ≠ z`, then it contains `2 * x` for each
of its elements `x`. Otherwise each line through the non-absolute point `x` would carry exactly
one absolute point: `(c, b) ↦ 2 * (b - c + x)` maps the disjoint union of the sets of
`odd_card_midpoints` for the residues `2 * c - 2 * x`, `c` in the set, injectively into the set,
although each of them is nonempty and the one for `c = x` contains both `y` and `z`. -/
private lemma two_mul_mem_of_two_mul_mem {v : ℕ} {D : Finset (ZMod v)}
    (hD : UniqueDifferences D) (hodd : ¬ 2 ∣ D.card) (hv : Odd v) {y z : D} (hyz : y ≠ z)
    (hy : 2 * (y : ZMod v) ∈ D) (hz : 2 * (z : ZMod v) ∈ D) (x : D) :
    2 * (x : ZMod v) ∈ D := by
  by_contra hx
  have hpos (c : D) :
      1 ≤ Fintype.card {b : D // 2 * (b : ZMod v) - (2 * c - 2 * x) ∈ D} := by
    have := odd_card_midpoints hD hodd (2 * c - 2 * x)
    omega
  have htwo : 1 < Fintype.card {b : D // 2 * (b : ZMod v) - (2 * x - 2 * x) ∈ D} := by
    rw [Fintype.one_lt_card_iff]
    refine ⟨⟨y, by simpa using hy⟩, ⟨z, by simpa using hz⟩, fun h => hyz ?_⟩
    exact congrArg Subtype.val h
  let g : (Σ c : D, {b : D // 2 * (b : ZMod v) - (2 * c - 2 * x) ∈ D}) → D := fun cb =>
    ⟨2 * (((cb.2 : D) : ZMod v) - cb.1 + x), by
      have e : 2 * (((cb.2 : D) : ZMod v) - cb.1 + x) =
          2 * ((cb.2 : D) : ZMod v) - (2 * cb.1 - 2 * x) := by ring
      rw [e]
      exact cb.2.property⟩
  have hg : Function.Injective g := by
    rintro ⟨c, b, hb⟩ ⟨c', b', hb'⟩ h
    have h2 : 2 * ((b : ZMod v) - c + x) = 2 * ((b' : ZMod v) - c' + x) :=
      congrArg Subtype.val h
    have heq : (b : ZMod v) - c = b' - c' := add_right_cancel (cancel_two hv h2)
    have hbc : b ≠ c := by
      rintro rfl
      apply hx
      simpa using hb
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (pair_eq hD hbc heq)
    rfl
  have hle := Fintype.card_le_of_injective g hg
  rw [Fintype.card_sigma] at hle
  have hlt : Fintype.card D <
      ∑ c : D, Fintype.card {b : D // 2 * (b : ZMod v) - (2 * c - 2 * x) ∈ D} :=
    calc Fintype.card D = ∑ _c : D, 1 := by simp
      _ < _ := Finset.sum_lt_sum (fun c _ => hpos c) ⟨x, Finset.mem_univ _, htwo⟩
  omega

/-- The Sidon set `{1, 2, 4, 8, 13}` has no extension of odd size: `2 * 1` and `2 * 2` lie in the
set, hence so does `2 * 8 = 16` by `two_mul_mem_of_two_mul_mem`, and then `16 - 13 = 4 - 1`
repeats a difference. -/
private lemma no_extension_of_odd_card {v : ℕ} {D : Finset (ZMod v)} (hD : UniqueDifferences D)
    (hodd : ¬ 2 ∣ D.card) (hv : Odd v) (hlt : 16 < v)
    (h1 : 1 ∈ D) (h2 : 2 ∈ D) (h4 : 4 ∈ D) (h8 : 8 ∈ D) (h13 : 13 ∈ D) : False := by
  have distinct := natCast_ne_of_lt (v := v)
  let one : D := ⟨1, h1⟩
  let two : D := ⟨2, h2⟩
  let four : D := ⟨4, h4⟩
  let thirteen : D := ⟨13, h13⟩
  have h12 : one ≠ two := fun e => distinct 1 2 (by omega) (by omega) (by decide)
    (by simpa [one, two] using congrArg Subtype.val e)
  have h16 : (16 : ZMod v) ∈ D := by
    have h := two_mul_mem_of_two_mul_mem hD hodd hv h12 (by simpa [one] using h2)
      (by change 2 * (2 : ZMod v) ∈ D; norm_num; exact h4) ⟨8, h8⟩
    change 2 * (8 : ZMod v) ∈ D at h
    norm_num at h
    exact h
  let sixteen : D := ⟨16, h16⟩
  have hne : sixteen ≠ thirteen := fun e => distinct 16 13 hlt (by omega) (by decide)
    (by simpa [sixteen, thirteen] using congrArg Subtype.val e)
  have hp := pair_eq hD hne (c := four) (d := one)
    (by change (16 : ZMod v) - 13 = 4 - 1; ring)
  apply distinct 16 4 hlt (by omega) (by decide)
  simpa [sixteen, four] using congrArg (fun ab : D × D => (ab.1 : ZMod v)) hp

/--
**The weak form of Erdős Problem 707 is false.** It is not the case that every finite Sidon set
$A \subseteq \mathbb{N}$ is contained in a perfect difference set modulo $m^2 + m + 1$ for some
natural number $m \ge 1$: there is a finite Sidon set $A \subseteq \mathbb{N}$ such that for every
$m \ge 1$, no set $B \subseteq \mathbb{N}$ with $A \subseteq B$ is a perfect difference set modulo
$m^2 + m + 1$. Here $A$ is Sidon when $w + x = y + z$ with $w, x, y, z \in A$ forces
$\{w, x\} = \{y, z\}$, and $B$ is a perfect difference set modulo $v$ when every nonzero residue
$r$ modulo $v$ satisfies $r \equiv a - b \pmod{v}$ for exactly one ordered pair $(a, b)$ of
elements of $B$.

Alexeev and Mixon proved that the Sidon set $\{1, 2, 4, 8, 13\}$ is contained in no perfect
difference set, and Hall (1947) proved the same for $\{1, 3, 9, 10, 13\}$.

Source: T. F. Bloom, Erdős Problems, Problem #707,
https://www.erdosproblems.com/707 (status DISPROVED (LEAN)); resolution: B. Alexeev and D. G. Mixon,
Forbidden Sidon subsets of perfect difference sets, featuring a human-assisted proof,
arXiv:2510.19804 (2025); M. Hall, Jr., Cyclic projective planes, Duke Math. J. 14 (1947), 1079-1090,
abstract of arXiv:2510.19804: {1, 2, 4, 8, 13} is a finite Sidon set contained in no finite perfect
difference set; erdosproblems.com/707: {1, 2, 4, 8} cannot be extended to a perfect difference set
modulo p² + p + 1 for any prime p, and Hall's {1, 3, 9, 10, 13} cannot be extended to any perfect
difference set, https://arxiv.org/abs/2510.19804.
-/
public theorem sidonExtendsToPerfectDifferenceSet_refuted :
    ¬ sidonExtendsToPerfectDifferenceSet := by
  classical
  let A : Set ℕ := {1, 2, 4, 8, 13}
  have hfin : A.Finite := by simp [A]
  have hsidon : A.IsSidon := by
    intro a ha b hb c hc d hd
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc hd
    omega
  intro hext
  obtain ⟨m, hm, B, hAB, hB⟩ := hext A hfin hsidon
  have h1 : 1 ∈ B := hAB (by simp [A])
  have h2 : 2 ∈ B := hAB (by simp [A])
  have h4 : 4 ∈ B := hAB (by simp [A])
  have h8 : 8 ∈ B := hAB (by simp [A])
  obtain rfl | rfl | hm3 : m = 1 ∨ m = 2 ∨ 3 ≤ m := by omega
  · -- Modulo `3`, the residues of `4` and `1` agree.
    have collision : (2, 1) = (2, 4) :=
      (hB 1 (by decide)).unique ⟨h2, h1, by decide⟩ ⟨h2, h4, by decide⟩
    contradiction
  · -- Modulo `7`, the residues of `8` and `1` agree.
    have collision : (2, 1) = (2, 8) :=
      (hB 1 (by decide)).unique ⟨h2, h1, by decide⟩ ⟨h2, h8, by decide⟩
    contradiction
  · let v := m ^ 2 + m + 1
    let D := Finset.univ.filter (fun z : ZMod v => ∃ b ∈ B, (b : ZMod v) = z)
    have hmem (z : ZMod v) : z ∈ D ↔ ∃ b ∈ B, (b : ZMod v) = z := by simp [D]
    have hD := uniqueDifferences_of_image hB hmem
    have hcard := card_of_uniqueDifferences hD (by omega : 0 < m)
    have mem {n : ℕ} (hn : n ∈ A) : (n : ZMod v) ∈ D := (hmem _).2 ⟨n, hAB hn, rfl⟩
    have hv : Odd v := by
      have h := Nat.even_mul_succ_self m
      exact (show Even (m ^ 2 + m) by convert h using 1; ring).add_one
    rcases Nat.even_or_odd m with heven | hodd
    · -- The extension has an odd number `m + 1` of elements.
      have hm2 := Nat.even_iff.mp heven
      have hm4 : 4 ≤ m := by omega
      apply no_extension_of_odd_card hD
      · rw [hcard]
        omega
      · exact hv
      · show 16 < m ^ 2 + m + 1
        nlinarith
      · simpa using mem (n := 1) (by simp [A])
      · simpa using mem (n := 2) (by simp [A])
      · simpa using mem (n := 4) (by simp [A])
      · simpa using mem (n := 8) (by simp [A])
      · simpa using mem (n := 13) (by simp [A])
    · -- The extension has an even number `m + 1` of elements.
      apply no_extension_odd hD
      · rw [hcard]
        exact even_iff_two_dvd.mp hodd.add_one
      · exact hv
      · show 8 < m ^ 2 + m + 1
        nlinarith
      · simpa using mem (n := 1) (by simp [A])
      · simpa using mem (n := 2) (by simp [A])
      · simpa using mem (n := 4) (by simp [A])
      · simpa using mem (n := 8) (by simp [A])

end MathlibExt.Combinatorics.SidonPerfectDifferenceSetErdosProblem707Wanted

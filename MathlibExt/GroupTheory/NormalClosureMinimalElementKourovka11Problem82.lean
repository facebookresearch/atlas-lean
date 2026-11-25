/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.Group

/-!
# Shortest elements of normal closures in free groups

The theorem `minimalNormalClosureElementConj_refuted` gives a counterexample to Kourovka 11.82
in the free group on $a,b$. Killing the relator $a^4 b a^2 b$ gives $b^2 = a^{-6}$, so the
length-six word $b^2 a b^{-2} a^{-1}$ lies in its normal closure. A homomorphism to the product
of a dihedral group and the integers detects every shorter nontrivial word. A second homomorphism,
to the wreath product of cyclic groups of orders four and three, separates the conjugacy classes.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.82 (V. N.
Remeslennikov). UnsolvedMath record UM-00700774 (`KOU-11.82`), dataset ulamai/UnsolvedMath v1.8.0.

The length is the reduced word length `FreeGroup.norm`. "Minimal length in `R`" is among the
nontrivial elements of `R` (the identity has length 0 and is `[r, 1]`), and `r ≠ 1`. Commutators
follow the source convention `[x, y] = x⁻¹ y⁻¹ x y`. The free group has an arbitrary basis `α :
Type`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82Wanted

/-- **Shortest elements of normal closures in free groups (Kourovka 11.82, Remeslennikov).** The
statement that for every free group $F$ and every $r \ne 1$ in $F$, if $s$ is a nontrivial element
of the normal closure $R$ of $r$ in $F$ whose reduced word length is minimal among the nontrivial
elements of $R$, then $s$ is conjugate to $r$, to $r^{-1}$, or, for some $f \in F$, to
$[r, f] = r^{-1} f^{-1} r f$ or to $[r^{-1}, f] = r f^{-1} r^{-1} f$. -/
def minimalNormalClosureElementConj : Prop :=
  ∀ (α : Type) [DecidableEq α] (r : FreeGroup α), r ≠ 1 →
    ∀ s ∈ Subgroup.normalClosure {r}, s ≠ 1 →
    (∀ t ∈ Subgroup.normalClosure {r}, t ≠ 1 → s.norm ≤ t.norm) →
    IsConj s r ∨ IsConj s r⁻¹ ∨
      ∃ f : FreeGroup α, IsConj s (r⁻¹ * f⁻¹ * r * f) ∨ IsConj s (r * f⁻¹ * r⁻¹ * f)

private abbrev F := FreeGroup Bool
private def a : F := FreeGroup.of false
private def b : F := FreeGroup.of true
private def relator : F := a ^ 4 * b * a ^ 2 * b
private def shortest : F := b ^ 2 * a * (b ^ 2)⁻¹ * a⁻¹

-- In the quotient, (a² b)² = a⁻². Thus a² commutes with a² b and with b,
-- giving b² = a⁻⁶, which commutes with a.
private theorem square_commutes {G : Type*} [Group G] (u v : G)
    (h : u ^ 4 * v * u ^ 2 * v = 1) : Commute (v ^ 2) u := by
  have hs : (u ^ 2 * v) ^ 2 = (u ^ 2)⁻¹ := by
    calc
      _ = (u ^ 2)⁻¹ * (u ^ 4 * v * u ^ 2 * v) := by rw [sq (u ^ 2 * v)]; group
      _ = _ := by rw [h, mul_one]
  have hc := Commute.self_pow (u ^ 2 * v) 2
  rw [hs, Commute.inv_right_iff] at hc
  have hc' : Commute v (u ^ 2) := by
    apply mul_left_cancel (a := u ^ 2)
    simpa only [mul_assoc] using hc.eq
  have hv : v ^ 2 = (u ^ 6)⁻¹ := by
    calc
      _ = (u ^ 6)⁻¹ * (u ^ 4 * (u ^ 2 * v) * v) := by rw [sq v]; group
      _ = _ := by rw [← hc'.eq, ← mul_assoc (u ^ 4), h, mul_one]
  rw [hv]
  exact (Commute.pow_self u 6).inv_left

private theorem shortest_mem : shortest ∈ Subgroup.normalClosure {relator} := by
  let N := Subgroup.normalClosure ({relator} : Set F)
  let q := QuotientGroup.mk' N
  have hr : q relator = 1 := (QuotientGroup.eq_one_iff _).2
    (Subgroup.subset_normalClosure (Set.mem_singleton _))
  simp only [relator, map_mul, map_pow] at hr
  apply (QuotientGroup.eq_one_iff (N := N) _).1
  change q shortest = 1
  simp only [shortest, map_mul, map_pow, map_inv]
  rw [(square_commutes _ _ hr).eq]
  group

-- The dihedral projection distinguishes the two reflections, and the integer
-- coordinate retains the exponent sum with weights 1 and -3.
private def detector : F →* DihedralGroup 5 × Multiplicative ℤ :=
  FreeGroup.lift fun g => if g then ⟨.sr 1, .ofAdd (-3)⟩ else ⟨.sr 0, .ofAdd 1⟩

private abbrev Letter := Bool × Bool

private def wordsUpTo : ℕ → List (List Letter)
  | 0 => [[]]
  | n + 1 => [] :: [(false, false), (false, true), (true, false), (true, true)].flatMap
      fun c => (wordsUpTo n).map (c :: ·)

private theorem mem_wordsUpTo (w : List Letter) (n : ℕ) (hw : w.length ≤ n) :
    w ∈ wordsUpTo n := by
  induction n generalizing w with
  | zero => simp_all [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons c cs =>
      have hcs := ih cs (by simpa using hw)
      obtain ⟨i, j⟩ := c
      cases i <;> cases j <;> simp [wordsUpTo, hcs]

-- Exhaust the words of length at most five, including unreduced representatives.
set_option maxRecDepth 8192 in
private theorem detects_short_words :
    ∀ l ∈ wordsUpTo 5, detector (FreeGroup.mk l) = 1 → FreeGroup.mk l = 1 := by decide

private theorem shortest_minimal (w : F) (hw : w ∈ Subgroup.normalClosure {relator})
    (hne : w ≠ 1) : shortest.norm ≤ w.norm := by
  have hr : detector relator = 1 := by decide
  have hle : Subgroup.normalClosure {relator} ≤ detector.ker :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hr)
  have hs : shortest.norm = 6 := by decide
  rw [hs]
  by_contra! h
  have hm := mem_wordsUpTo w.toWord 5 (by change w.norm ≤ 5; omega)
  have hdet : detector w = 1 := hle hw
  have hshort := detects_short_words _ hm
  rw [FreeGroup.mk_toWord] at hshort
  exact hne (hshort hdet)

-- In C₄ ≀ C₃ the image of a rotates the three coordinates, and b adds 1
-- at the identity coordinate. Thus r adds 1 at two coordinates, while s
-- adds 2 at the identity. Conjugation only rotates a base element's coordinates.
private abbrev Lamp := Multiplicative (ZMod 4)
private abbrev Position := Multiplicative (ZMod 3)
private abbrev W := Lamp ≀ᵣ Position

private def lamps : F →* W := FreeGroup.lift fun g =>
  if g then ⟨fun i => if i = 1 then .ofAdd 1 else 1, 1⟩
  else ⟨1, .ofAdd 1⟩

private theorem conj_left (g x : W) (hx : x.right = 1) (i : Position) :
    (g * x * g⁻¹).left i = x.left (g.right⁻¹ * i) := by
  simp [hx, mul_comm]

private theorem mul_conj_left (x y g : W) (hx : x.right = 1) (hy : y.right = 1)
    (i : Position) : (x * g⁻¹ * y * g).left i = x.left i * y.left (g.right * i) := by
  have h : (g⁻¹ * y * g).left i = y.left (g.right * i) := by
    simpa only [inv_inv, RegularWreathProduct.inv_right] using conj_left g⁻¹ y hy i
  rw [mul_assoc x g⁻¹ y, mul_assoc x _ g, RegularWreathProduct.mul_left, Pi.mul_apply]
  simpa only [hx, inv_one, one_mul] using congrArg (x.left i * ·) h

private theorem not_conjugate (v : F) (hv : ∀ i, (lamps v).left i ≠ .ofAdd 2) :
    ¬ IsConj shortest v := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he := congrArg lamps hg
  simp only [map_mul, map_inv] at he
  have hs : (lamps shortest).right = 1 := by decide
  have hi := congrArg (fun y : W => y.left (lamps g).right) he
  rw [conj_left _ _ hs, inv_mul_cancel] at hi
  exact hv _ (hi.symm.trans (by decide))

private theorem exclusions :
    ¬ (IsConj shortest relator ∨ IsConj shortest relator⁻¹ ∨
      ∃ f : F, IsConj shortest (relator⁻¹ * f⁻¹ * relator * f) ∨
        IsConj shortest (relator * f⁻¹ * relator⁻¹ * f)) := by
  have hr : (lamps relator).right = 1 := by decide
  have hi : (lamps relator)⁻¹.right = 1 := by simp [hr]
  have values : ∀ i j : Position,
      (lamps relator).left i ≠ .ofAdd 2 ∧
      (lamps relator)⁻¹.left i ≠ .ofAdd 2 ∧
      (lamps relator)⁻¹.left i * (lamps relator).left j ≠ .ofAdd 2 ∧
      (lamps relator).left i * (lamps relator)⁻¹.left j ≠ .ofAdd 2 := by decide
  rintro (h | h | ⟨f, h | h⟩)
  · exact not_conjugate _ (fun i => (values i i).1) h
  · exact not_conjugate _ (fun i => by rw [map_inv]; exact (values i i).2.1) h
  · apply not_conjugate _ _ h
    intro i
    simp only [map_mul, map_inv, mul_conj_left _ _ _ hi hr]
    exact (values i _).2.2.1
  · apply not_conjugate _ _ h
    intro i
    simp only [map_mul, map_inv, mul_conj_left _ _ _ hr hi]
    exact (values i _).2.2.2

/--
**Negative answer to Kourovka 11.82 on shortest elements of normal closures.** There are a free
group $F$, an element $r \ne 1$ of $F$, and a nontrivial element $s$ of the normal closure $R$ of
$r$ in $F$ whose reduced word length is minimal among the nontrivial elements of $R$, such that $s$
is conjugate neither to $r$ nor to $r^{-1}$, nor, for any $f \in F$, to
$[r, f] = r^{-1} f^{-1} r f$ or to $[r^{-1}, f] = r f^{-1} r^{-1} f$.

The Kourovka Archive answers 11.82 "No, not always" (McCool).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.82 (V. N.
Remeslennikov); resolution: J. McCool, Glasgow Math. J. 43, no. 1 (2001), 123-124, Kourovka Archive,
Problem 11.82: "No, not always", https://arxiv.org/abs/1401.0300v49.
-/
theorem minimalNormalClosureElementConj_refuted : ¬ minimalNormalClosureElementConj := by
  intro h
  exact exclusions (h Bool relator (by decide) shortest shortest_mem (by decide) shortest_minimal)

end MathlibExt.GroupTheory.NormalClosureMinimalElementKourovka11Problem82Wanted

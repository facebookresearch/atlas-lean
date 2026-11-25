/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Three-term progression-free sets meeting every infinite progression

We refute Erdős Problem 199 using the sum of squares of the rational Hamel coordinates of a real.
Its level sets are three-term progression-free, and along each progression it is a quadratic
polynomial with rational coefficients. We enumerate the countably many possible polynomials
and place parts of their level sets in separated intervals to meet every progression.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ThreeAPFreeComplementProgressionErdosProblem199Wanted

/-- **Erdős Problem 199.** The statement that for every set $A \subseteq \mathbb{R}$ containing no
three-term arithmetic progression (no $x, y, z \in A$ with $x + z = 2y$ and $x \ne y$) there are
reals $a$ and $d \ne 0$ with $a + nd \notin A$ for every natural number $n$, that is, the
complement $\mathbb{R} \setminus A$ contains the infinite arithmetic progression
$a, a + d, a + 2d, \dots$. -/
def threeAPFreeComplementContainsProgression : Prop :=
  ∀ A : Set ℝ, ThreeAPFree A → ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, a + n * d ∉ A

private noncomputable abbrev coords := (Module.Basis.ofVectorSpace ℚ ℝ).repr

private noncomputable def energy (x : ℝ) : ℚ := (coords x).sum fun _ t ↦ t ^ 2

/-- Along a nonconstant progression the coordinate sum of squares is strictly quadratic. -/
private lemma energy_on_progression (a d : ℝ) (hd : d ≠ 0) :
    ∃ u v w : ℚ, 0 < w ∧ ∀ n : ℕ, energy (a + n * d) = u + n * v + n ^ 2 * w := by
  classical
  let s := (coords a).support ∪ (coords d).support
  have hne : coords d ≠ 0 := by simpa using hd
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hi' : i ∈ (coords d).support := Finsupp.mem_support_iff.mpr hi
  refine ⟨∑ i ∈ s, coords a i ^ 2, ∑ i ∈ s, 2 * coords a i * coords d i,
    ∑ i ∈ s, coords d i ^ 2, Finset.sum_pos' (fun _ _ ↦ sq_nonneg _)
      ⟨i, Finset.mem_union_right _ hi', sq_pos_of_ne_zero hi⟩, fun n ↦ ?_⟩
  have hcoords : coords (a + n * d) = coords a + n • coords d := by
    rw [← nsmul_eq_mul, map_add, map_nsmul]
  rw [energy, hcoords, Finsupp.sum_of_support_subset _ (s := s)
    (Finsupp.support_add.trans (Finset.union_subset_union_right Finsupp.support_smul)) _
    (by simp)]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, Finsupp.add_apply, Finsupp.smul_apply,
    nsmul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

private lemma energy_level_free (r : ℚ) : ThreeAPFree {x | energy x = r} := by
  intro x hx y hy z hz heq
  change energy x = r at hx
  change energy y = r at hy
  change energy z = r at hz
  by_contra hxy
  obtain ⟨u, v, w, hw, h⟩ := energy_on_progression x (y - x) (sub_ne_zero.mpr (Ne.symm hxy))
  have h₂ : x + 2 * (y - x) = z := by linarith
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [h₂, hx, hy, hz] at h0 h1 h2
  linarith

/-- The rational data shared by a family of progressions. After multiplying by `scale`,
the starting points have absolute value at most `bound` and the steps lie between 5 and 6. -/
private structure Profile where
  scale : ℚ
  bound : ℕ
  constCoeff : ℚ
  linCoeff : ℚ
  quadCoeff : ℚ
  deriving Inhabited, Countable

private def slice (p : Profile) (n : ℕ) : Set ℝ :=
  {x | 4 * (n : ℝ) < p.scale * x ∧ p.scale * x < 7 * n ∧
    energy x = p.constCoeff + n * p.linCoeff + n ^ 2 * p.quadCoeff}

/-- Two separated intervals cannot contribute a mixed three-term progression. -/
private lemma free_union {S T : Set ℝ} (hS : ThreeAPFree S) (hT : ThreeAPFree T)
    {q b : ℝ} (hs : ∀ x ∈ S, -b < q * x ∧ q * x < b)
    (ht : ∀ x ∈ T, 4 * b < q * x ∧ q * x < 7 * b) : ThreeAPFree (S ∪ T) := by
  intro x hx y hy z hz heq
  have hsum : q * x + q * z = q * y + q * y := by rw [← mul_add, ← mul_add, heq]
  have locate {t : ℝ} (ht' : t ∈ S ∪ T) :
      (t ∈ S ∧ -b < q * t ∧ q * t < b) ∨ (t ∈ T ∧ 4 * b < q * t ∧ q * t < 7 * b) :=
    ht'.imp (fun h ↦ ⟨h, hs t h⟩) (fun h ↦ ⟨h, ht t h⟩)
  rcases locate hx with ⟨hx, hx₁, hx₂⟩ | ⟨hx, hx₁, hx₂⟩ <;>
    rcases locate hy with ⟨hy, hy₁, hy₂⟩ | ⟨hy, hy₁, hy₂⟩ <;>
    rcases locate hz with ⟨hz, hz₁, hz₂⟩ | ⟨hz, hz₁, hz₂⟩
  all_goals first | exact hS hx hy hz heq | exact hT hx hy hz heq | linarith

private structure Stage where
  points : Set ℝ
  free : ThreeAPFree points
  bounded : ∃ B : ℝ, ∀ x ∈ points, |x| ≤ B

private lemma extend_stage (S : Stage) (p : Profile) :
    ∃ T : Stage, S.points ⊆ T.points ∧ ∃ n > p.bound, slice p n ⊆ T.points := by
  obtain ⟨B, hB⟩ := S.bounded
  let q : ℝ := p.scale
  obtain ⟨n, hn⟩ := exists_nat_gt (max (p.bound : ℝ) (|q| * B))
  obtain ⟨hn₁, hn₂⟩ := max_lt_iff.mp hn
  have hS (x) (hx : x ∈ S.points) : -(n : ℝ) < q * x ∧ q * x < n := by
    apply abs_lt.mp
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg q)).trans_lt hn₂
  have hT (x) (hx : x ∈ slice p n) : 4 * (n : ℝ) < q * x ∧ q * x < 7 * n :=
    ⟨hx.1, hx.2.1⟩
  have hfree : ThreeAPFree (slice p n) := (energy_level_free _).mono fun _ hx ↦ hx.2.2
  refine ⟨⟨S.points ∪ slice p n, free_union S.free hfree hS hT, ?_⟩,
    Set.subset_union_left, n, by exact_mod_cast hn₁, Set.subset_union_right⟩
  refine ⟨max B (7 * n / |q|), fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hB x hx).trans (le_max_left ..)
  · obtain ⟨hlo, hhi⟩ := hT x hx
    have hpos : 0 < q * x := lt_of_le_of_lt (by positivity) hlo
    have hq : q ≠ 0 := left_ne_zero_of_mul hpos.ne'
    apply le_trans _ (le_max_right ..)
    apply (le_div_iff₀ (abs_pos.mpr hq)).mpr
    rw [mul_comm, ← abs_mul, abs_of_pos hpos]
    exact hhi.le

/-- Enumerating the profiles gives an increasing union which contains a slice for each one. -/
private lemma exists_free_set :
    ∃ A : Set ℝ, ThreeAPFree A ∧ ∀ p : Profile, ∃ n > p.bound, slice p n ⊆ A := by
  classical
  obtain ⟨f, hf⟩ := exists_surjective_nat Profile
  let stages : ℕ → Stage := Nat.rec ⟨∅, threeAPFree_empty, 0, by simp⟩
    (fun i S ↦ (extend_stage S (f i)).choose)
  have hstep (i : ℕ) := (extend_stage (stages i) (f i)).choose_spec
  have hmono : Monotone fun i ↦ (stages i).points :=
    monotone_nat_of_le_succ fun i ↦ (hstep i).1
  refine ⟨⋃ i, (stages i).points, ?_, ?_⟩
  · intro x hx y hy z hz heq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    let m := max i (max j k)
    exact (stages m).free (hmono (show i ≤ m by simp [m]) hi)
      (hmono (show j ≤ m by simp [m]) hj) (hmono (show k ≤ m by simp [m]) hk) heq
  · intro p
    obtain ⟨i, rfl⟩ := hf p
    obtain ⟨n, hn, hsub⟩ := (hstep i).2
    exact ⟨n, hn, hsub.trans (Set.subset_iUnion (fun j ↦ (stages j).points) (i + 1))⟩

private lemma exists_scale (d : ℝ) (hd : d ≠ 0) : ∃ q : ℚ, 5 < q * d ∧ q * d < 6 := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn
      (show 6 / d < 5 / d from div_lt_div_of_neg_of_lt hneg (by norm_num))
    exact ⟨q, (lt_div_iff_of_neg hneg).mp hhi, (div_lt_iff_of_neg hneg).mp hlo⟩
  · obtain ⟨q, hlo, hhi⟩ := exists_rat_btwn
      (show 5 / d < 6 / d from div_lt_div_of_pos_right (by norm_num) hpos)
    exact ⟨q, (div_lt_iff₀ hpos).mp hlo, (lt_div_iff₀ hpos).mp hhi⟩

/--
**Erdős Problem 199 is false.** There is a set $A \subseteq \mathbb{R}$ containing no three-term
arithmetic progression (no $x, y, z \in A$ with $x + z = 2y$ and $x \ne y$) such that for all reals
$a$ and $d \ne 0$ some term $a + nd$, with $n$ a natural number, lies in $A$: the complement
$\mathbb{R} \setminus A$ contains no infinite arithmetic progression $a, a + d, a + 2d, \dots$
with $d \ne 0$.

Baumgartner constructed such a set with the axiom of choice, from a basis of $\mathbb{R}$ over
$\mathbb{Q}$.

Source: T. F. Bloom, Erdős Problems, Problem #199,
https://www.erdosproblems.com/199 (status DISPROVED (LEAN)); resolution: J. E. Baumgartner,
Partitioning vector spaces, J. Combin. Theory Ser. A 18 (1975), 231-233; formal proof
plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos199.lean, erdosproblems.com/199: answered no by
Baumgartner (construction using a Hamel basis), https://doi.org/10.1016/0097-3165(75)90011-8.
-/
public theorem threeAPFreeComplementContainsProgression_refuted :
    ¬ threeAPFreeComplementContainsProgression := by
  intro h
  obtain ⟨A, hA, hslices⟩ := exists_free_set
  obtain ⟨a, d, hd, hmiss⟩ := h A hA
  obtain ⟨u, v, w, _, hpoly⟩ := energy_on_progression a d hd
  obtain ⟨q, hq₁, hq₂⟩ := exists_scale d hd
  obtain ⟨b, hb⟩ := exists_nat_gt |(q : ℝ) * a|
  obtain ⟨n, hn, hsub⟩ := hslices ⟨q, b, u, v, w⟩
  have hbound : |(q : ℝ) * a| < n := hb.trans (by exact_mod_cast hn : (b : ℝ) < n)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hbound
  apply hmiss n (hsub _)
  refine ⟨?_, ?_, hpoly n⟩
  · dsimp
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hq₁.le)]
  · dsimp
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hq₂.le)]

end MathlibExt.Combinatorics.ThreeAPFreeComplementProgressionErdosProblem199Wanted

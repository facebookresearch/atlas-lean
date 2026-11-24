/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import MathlibExt.Combinatorics.CleanLatticeParallelogram

/-!
# Paired columns of a clean lattice parallelogram

Point reflection exchanges the lowest and highest interior lattice points on paired columns
and preserves the boundary of the convex hull of the interior lattice points.
-/

namespace MetaMathlibExt

namespace stdColumn_low_add_high

private abbrev reflection (a n : ℕ) := Homeomorph.subLeft ((a + 1 : ℝ), (n : ℝ))

private theorem preimage_eq_self {a n : ℕ} {s : Set (ℝ × ℝ)}
    (hs : Set.MapsTo (reflection a n) s s) : reflection a n ⁻¹' s = s := by
  ext p
  exact ⟨fun hp => (sub_sub_cancel ((a + 1 : ℝ), (n : ℝ)) p) ▸ hs hp, fun hp => hs hp⟩

private theorem preimage_interior (a n : ℕ) :
    reflection a n ⁻¹' interior (stdCleanParallelogram a n) =
      interior (stdCleanParallelogram a n) := by
  rw [Homeomorph.preimage_interior]
  congr 1
  apply preimage_eq_self
  rintro _ ⟨s, t, hs₀, hs₁, ht₀, ht₁, rfl⟩
  refine ⟨1 - s, 1 - t, sub_nonneg.mpr hs₁, sub_le_self _ hs₀,
    sub_nonneg.mpr ht₁, sub_le_self _ ht₀, ?_⟩
  ext <;> simp [reflection, Homeomorph.subLeft, sub_smul, Prod.smul_mk, smul_eq_mul]
  ring

private theorem preimage_frontier_hull (a n : ℕ) :
    let H := convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints)
    reflection a n ⁻¹' frontier H = frontier H := by
  dsimp only
  rw [Homeomorph.preimage_frontier]
  congr 1
  have inv : Function.Involutive (reflection a n) := fun p => sub_sub_cancel _ p
  have hull (s : Set (ℝ × ℝ)) :
      reflection a n ⁻¹' convexHull ℝ s = convexHull ℝ (reflection a n ⁻¹' s) := by
    rw [← inv.image_eq_preimage_symm]
    exact (AffineEquiv.constVSub ℝ ((a + 1 : ℝ), (n : ℝ))).toAffineMap.image_convexHull s
  rw [hull, Set.preimage_inter, preimage_interior]
  suffices reflection a n ⁻¹' latticePoints = latticePoints by rw [this]
  apply preimage_eq_self
  rintro _ ⟨⟨i, j⟩, rfl⟩
  refine ⟨((a : ℤ) + 1 - i, (n : ℤ) - j), ?_⟩
  change (_, _) = (_, _)
  push_cast
  rfl

end stdColumn_low_add_high

open stdColumn_low_add_high

set_option linter.unusedVariables false in
/-- **Lowest and highest interior lattice points of $P_{a,n}$ on paired vertical lines.** Let $a$
and $n$ be natural numbers with $1 \le a < n$ and $\gcd(a, n) = 1$, let $P_{a,n}$ be the
parallelogram with vertices $(0, 0)$, $(1, 0)$, $(a, n)$, $(a + 1, n)$, and for an integer $k$
let $S_k$ be the set of integers $y$ such that $(k, y)$ lies in the interior of $P_{a,n}$. Let
$k, l \ge 1$ be natural numbers with $k + l = a + 1$, and suppose that $y_L$ is the least element
of $S_k$ and $y_H$ is the greatest element of $S_l$. Then $y_L + y_H = n$, and $(l, y_H)$ lies on
the boundary of the convex hull of the points of $\mathbb{Z}^2$ in the interior of $P_{a,n}$ if
and only if $(k, y_L)$ does.

Source: Gabriel Khan, Mizan R. Khan, Riaz R. Khan, and Peng Zhao, *A Geometric Relationship
between Continued Fractions and Clean Lattice Parallelograms*, INTEGERS 26 (2026), Article A10,
Lemma 6 (`integers-2026-A10-lem-6`). -/
public theorem stdColumn_low_add_high {a n : ℕ} (ha : 1 ≤ a) (han : a < n)
    (hcop : Nat.Coprime a n) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l = a + 1)
    {yL yH : ℤ} (hL : IsLeast (stdColumn a n k) yL) (hH : IsGreatest (stdColumn a n l) yH) :
    yL + yH = n ∧
      ((((l : ℝ), (yH : ℝ)) ∈
          frontier (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints))) ↔
        (((k : ℝ), (yL : ℝ)) ∈
          frontier (convexHull ℝ (interior (stdCleanParallelogram a n) ∩ latticePoints)))) := by
  have hx : (a : ℝ) + 1 - k = l := by
    have : (k : ℝ) + l = a + 1 := by exact_mod_cast hkl
    linarith
  have reflect_point (y : ℤ) :
      reflection a n ((k : ℝ), (y : ℝ)) = ((l : ℝ), (((n : ℤ) - y : ℤ) : ℝ)) := by
    change (_, _) = (_, _)
    simp only [hx, Int.cast_sub, Int.cast_natCast]
  have column (y : ℤ) : (n : ℤ) - y ∈ stdColumn a n l ↔ y ∈ stdColumn a n k := by
    simpa only [stdColumn, Set.mem_ofPred_eq, Int.cast_natCast, Set.mem_preimage, reflect_point]
      using Set.ext_iff.mp (preimage_interior a n) ((k : ℝ), (y : ℝ))
  have lower := hH.2 ((column yL).mpr hL.1)
  have upper := hL.2 ((column (n - yH)).mp (by simpa only [sub_sub_cancel] using hH.1))
  have hy : (n : ℤ) - yL = yH := by omega
  refine ⟨by omega, ?_⟩
  simpa only [Set.mem_preimage, reflect_point, hy] using
    Set.ext_iff.mp (preimage_frontier_hull a n) ((k : ℝ), (yL : ℝ))

end MetaMathlibExt

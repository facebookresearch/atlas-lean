/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive
public import MathlibExt.Geometry.LatticePointEnumerator

/-!
# Ehrhart functions and $h^*$-polynomials

The Ehrhart function counts the integer points in a dilate. Its generating series defines the
$h^*$-polynomial independently of any formula for weighted simplices.

## References

* Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
  Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
  p. 3 (unimodality) and Section 2.3 (Ehrhart theory).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ehrhart function.** For a finite index set $\iota$, a set $P \subseteq \mathbb{R}^\iota$
and a natural number $t$, the Ehrhart function $L_P(t)$ is the number of integer vectors
$x \in \mathbb{Z}^\iota$ lying in the dilate $tP = \{t y : y \in P\}$, with the convention that
$L_P(t) = 0$ when there are infinitely many such vectors.

No boundedness of $P$ is needed for the definition. On $\mathbb{R}^d$ it agrees with the
lattice-point enumerator of $P$ at the real dilate $t$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Section 2.3. -/
public noncomputable def ehrhart {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (t : ℕ) : ℕ :=
  Set.ncard {x : ι → ℤ | IsLatticePoint (polytopeDilate t P) x}

/-- **The Ehrhart function agrees with the lattice-point enumerator.** For every subset
$P \subseteq \mathbb{R}^d$ and every natural number $t$, the Ehrhart function of $P$ at $t$,
the number of integer vectors $x \in \mathbb{Z}^d$ lying in the dilate $tP$, equals the
lattice-point enumerator of $P$ at the real dilate $t$, the number of points of
$tP \cap \mathbb{Z}^d$. Both counts are taken to be $0$ when the set counted is infinite.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Section 2.3. -/
public theorem ehrhart_eq_latticeEnumerator {d : ℕ} (P : Set (Fin d → ℝ)) (t : ℕ) :
    ehrhart P t = LatticePointEnumerator.latticeEnumerator d P t := by
  have hinj : Function.Injective (fun x : Fin d → ℤ => fun i => (x i : ℝ)) := by
    intro x y h
    funext i
    simpa using congrFun h i
  unfold ehrhart LatticePointEnumerator.latticeEnumerator
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, IsLatticePoint, polytopeDilate,
    LatticePointEnumerator.latticePointSet, Set.mem_inter_iff, SetLike.mem_coe,
    LatticePointEnumerator.mem_stdLattice_iff, Set.mem_smul_set]
  constructor
  · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    refine ⟨⟨y, hy, ?_⟩, fun i => ⟨x i, rfl⟩⟩
    funext i
    simpa [smul_eq_mul] using (congrFun hxy i).symm
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    choose z hz using hz
    refine ⟨z, ⟨y, hy, ?_⟩, ?_⟩
    · funext i
      simpa [smul_eq_mul] using hz i
    · funext i
      exact hz i

/-- **The $h^*$-polynomial.** Let $P \subseteq \mathbb{R}^n$, with coordinates indexed by a finite
set of size $n$, and let $L_P(t)$ be the number of lattice points of the dilate
$tP = \{t y : y \in P\}$ (taken to be $0$ if there are infinitely many). A polynomial
$h \in \mathbb{Z}[z]$ is an $h^*$-polynomial of $P$ when
$$\Big(\sum_{t \ge 0} L_P(t)\, z^t\Big) (1 - z)^{n+1} = h(z)$$
as formal power series with integer coefficients.

The exponent uses the ambient dimension $n$, which is $\dim P$ when $P$ is full dimensional, and
$h^*$ is characterised by this identity rather than by the explicit formula for weighted simplices.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Section 2.3. -/
public def IsHStarPolynomial {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (h : Polynomial ℤ) : Prop :=
  PowerSeries.mk (fun t => (ehrhart P t : ℤ)) *
      (1 - PowerSeries.X) ^ (Fintype.card ι + 1) = (h : PowerSeries ℤ)

/-- **Unimodal polynomials.** A polynomial $p = \sum_k a_k z^k \in \mathbb{Z}[z]$ of degree $n$
(with $n = 0$ for $p = 0$) is unimodal when there is an index $t \le n$ such that
$a_0 \le a_1 \le \dots \le a_t$ and $a_t \ge a_{t+1} \ge \dots \ge a_n$.

The paper considers polynomials with nonnegative coefficients; the order condition itself is
stated over $\mathbb{Z}$.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, p. 3. -/
public def IsUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, t ≤ p.natDegree ∧
    (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → j ≤ p.natDegree → p.coeff j ≤ p.coeff i)

end

end MetaMathlibExt

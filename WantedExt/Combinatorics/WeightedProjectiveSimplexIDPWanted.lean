/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Geometry.LatticePointEnumerator

/-!
# The integer decomposition property and weighted projective space simplices (statements)

Statement-only targets from Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and
Liam Solus, *The Integer Decomposition Property and Weighted Projective Space Simplices*, for the
simplices `Δ_(1,q) = conv(e_1, …, e_n, -∑ q_i e_i)`. IDP, reflexivity, the Ehrhart function and
the `h*`-polynomial are defined geometrically (not by the paper's number-theoretic criteria), so
Theorems 1, 4 and 5 relate independent notions.
-/

namespace MetaMathlibExt

open Filter

@[expose] public section

/-! ## Basic geometric and enumerative definitions -/

/-- The weighted projective simplex with weights `q`: the convex hull of the
standard basis vectors and the vector whose `i`th coordinate is `-q i`.  The
latter is exactly `-∑ i, q i • e_i` after evaluating coordinates.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def weightedSimplex {n : ℕ} (q : Fin n → ℕ) : Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range (fun i : Fin n => Pi.single i (1 : ℝ)) ∪
    {fun i => -(q i : ℝ)})

/-- The scalar dilate `tP`.  The natural number is cast to `ℝ`, matching the
paper's nonnegative integral dilations.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public def polytopeDilate {ι : Type*} (t : ℕ) (P : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {x | ∃ y ∈ P, x = fun i => (t : ℝ) * y i}

/-- `x` is an integral point of `P` when its coordinatewise real coercion lies
in `P`; this makes the paper's intersection with `ℤⁿ` explicit.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public def IsLatticePoint {ι : Type*} (P : Set (ι → ℝ)) (x : ι → ℤ) : Prop :=
  (fun i => (x i : ℝ)) ∈ P

/-- The integer decomposition property: every lattice point of every positive
`m`th dilate is a coordinatewise sum of exactly `m` lattice points of `P`.
This is the height-by-height version of the paper's cone definition; for a
convex lattice polytope, the height-`m` slice of the cone is `m • P`.  It also
implements the paper's intended `(m,w)`, correcting its displayed `(k,w)` typo.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def HasIDP {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ w : ι → ℤ, IsLatticePoint (polytopeDilate m P) w →
    ∃ x : Fin m → ι → ℤ,
      (∀ k, IsLatticePoint P (x k)) ∧ (∀ i, ∑ k, x k i = w i)

/-- Reflexivity in the height-by-height form allowed in the task: an interior
lattice point `c` translates the lattice points of `(t-1)P` bijectively onto
the interior lattice points of `tP`, for every positive height `t`.  This is
the paper's cone/interior condition, not its later divisibility criterion.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def IsReflexive {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∃ c : ι → ℤ, IsLatticePoint (interior P) c ∧
    ∀ t : ℕ, 1 ≤ t → ∀ x : ι → ℤ,
      IsLatticePoint (interior (polytopeDilate t P)) x ↔
        ∃ y : ι → ℤ, IsLatticePoint (polytopeDilate (t - 1) P) y ∧
          x = fun i => c i + y i

/-- The Ehrhart function is the `Set.ncard` of the lattice points in `tP`.  It is stated
for an arbitrary finite coordinate type (free sums use `Sum (Fin n) (Fin m)`); on
`Fin d → ℝ` it agrees with the canonical `LatticePointEnumerator.latticeEnumerator`
(`ehrhart_eq_latticeEnumerator`).  `Set.ncard` makes this total even before
boundedness is supplied.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public noncomputable def ehrhart {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (t : ℕ) : ℕ :=
  Set.ncard {x : ι → ℤ | IsLatticePoint (polytopeDilate t P) x}

/-- On `Fin d → ℝ`, `ehrhart` is the canonical lattice-point enumerator
`LatticePointEnumerator.latticeEnumerator` at the real dilate `(t : ℝ)`: the integer points
of `polytopeDilate t P` correspond under the injective coercion `ℤ^d → ℝ^d` to
`(t • P) ∩ ℤ^d`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
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

/-- A polynomial `h` is an Ehrhart `h*`-polynomial of `P` when multiplication
of the Ehrhart power series by `(1-X)^(n+1)` gives the coerced polynomial.
This relation is used instead of defining `h*` by the formula in Theorem 5.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public def IsHStarPolynomial {ι : Type*} [Fintype ι]
    (P : Set (ι → ℝ)) (h : Polynomial ℤ) : Prop :=
  PowerSeries.mk (fun t => (ehrhart P t : ℤ)) *
      (1 - PowerSeries.X) ^ (Fintype.card ι + 1) = (h : PowerSeries ℤ)

/-- Polynomial unimodality: there is a coefficient index `t` up to the natural
degree such that coefficients are weakly increasing through `t` and weakly
decreasing thereafter.  The paper assumes nonnegative coefficients; the order
condition itself is stated over `ℤ`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def IsUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, t ≤ p.natDegree ∧
    (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → j ≤ p.natDegree → p.coeff j ≤ p.coeff i)

/-- A polytope is `h*`-unimodal when a polynomial satisfying the defining
Ehrhart-series identity is unimodal.  Thus this does not build `h*` from the
explicit weighted-simplex formula.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def IsHStarUnimodal {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) : Prop :=
  ∃ h : Polynomial ℤ, IsHStarPolynomial P h ∧ IsUnimodal h

/-! ## Weight and support notation -/

/-- Expands support values `r` with multiplicities `x`, in support-index order,
using `List.replicate`, exactly representing `(r₁^{x₁},…,r_d^{x_d})`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def expandSupport {d : ℕ} (r x : Fin d → ℕ) : List ℕ :=
  (List.ofFn fun i => List.replicate (x i) (r i)).flatten

/-- Valid support data means a nonempty support (`0 < d`, as `q` has at least one
entry in the paper), positive pairwise-distinct support entries and positive
multiplicities, spelling out the hypotheses implicit in `(r,x)`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def ValidSupport {d : ℕ} (r x : Fin d → ℕ) : Prop :=
  0 < d ∧ Function.Injective r ∧ (∀ i, 1 ≤ r i) ∧ (∀ i, 1 ≤ x i)

/-- The simplex attached to a list of weights, using the list's canonical
`Fin q.length` indexing.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public def weightedSimplexList (q : List ℕ) : Set (Fin q.length → ℝ) :=
  weightedSimplex q.get

/-- The least-common-multiple convention for a list of weights; starting the
fold at `1` gives the standard LCM and also assigns `1` to the empty list.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def weightLcm (q : List ℕ) : ℕ := q.foldl Nat.lcm 1

/-- Setup 1's integer `ℓ=(1+∑xᵢrᵢ)/lcm(r)`.  Natural division is exact under
the reflexivity hypothesis in the results that use this notation.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def setupEll {d : ℕ} (r x : Fin d → ℕ) : ℕ :=
  (1 + ∑ i, x i * r i) / weightLcm (List.ofFn r)

/-- Setup 1's complementary factor `sᵢ=lcm(r)/rᵢ`.  Positivity hypotheses in
the results ensure that this natural-number quotient is the intended one.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public def setupS {d : ℕ} (r : Fin d → ℕ) (i : Fin d) : ℕ :=
  weightLcm (List.ofFn r) / r i

/-- The paper's weight statistic `w(q,b)`.  Floors of nonnegative rational
numbers are natural divisions; subtraction is natural subtraction, which is
nontruncating on the stated range by the mathematical estimate behind the formula.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public def weightStatistic (q : List ℕ) (b : ℕ) : ℕ :=
  b - (q.map fun a => a * b / (1 + q.sum)).sum

/-- The explicit polynomial `∑_{b=0}^{∑qᵢ} z^{w(q,b)}` from Theorem 5.
It is named a formula, not defined to be `h*`; Theorem 5 relates it to the
independently defined Ehrhart-series condition.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public noncomputable def hStarFormula (q : List ℕ) : Polynomial ℤ :=
  ∑ b ∈ Finset.range (q.sum + 1), Polynomial.X ^ weightStatistic q b

/-- Setup 1's exponent `u(α)=αℓ-∑xᵢ⌊α/sᵢ⌋`, with each floor represented by
natural division.  Its use is restricted to positive valid setup data.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public def setupU {d : ℕ} (r x : Fin d → ℕ) (α : ℕ) : ℕ :=
  α * setupEll r x - ∑ i, x i * (α / setupS r i)

/-- The polynomial `g_r^x(z)=∑_{0≤α<lcm(r)} z^{u(α)}` from the paper.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public noncomputable def setupG {d : ℕ} (r x : Fin d → ℕ) : Polynomial ℤ :=
  ∑ α ∈ Finset.range (weightLcm (List.ofFn r)), Polynomial.X ^ setupU r x α

/-- The coordinate form of Definition `idpnecessary`: each weight `q j`
satisfies `1+∑ᵢ(qᵢ mod qⱼ)=qⱼ`.  `%` is the remainder in `[0,q j)`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public def SatisfiesIDPNecessary {n : ℕ} (q : Fin n → ℕ) : Prop :=
  ∀ j, 1 + ∑ i, q i % q j = q j

/-- The support/multiplicity form of the necessary condition:
`1+∑ᵢxᵢ(rᵢ mod rⱼ)=rⱼ` for every support index `j`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public def SatisfiesSupportIDPNecessary {d : ℕ} (r x : Fin d → ℕ) : Prop :=
  ∀ j, 1 + ∑ i, x i * (r i % r j) = r j

/-! ## Theorems 1--9 -/

/-- Theorem 1, coordinate form: for positive weights, geometric reflexivity is
equivalent to every `q i` dividing `1+∑q`.  The left side uses the independent
height-wise definition of reflexivity, so the statement is nontrivial.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public theorem_wanted reflexive_iff_weight_dvd {n : ℕ} (q : Fin n → ℕ)
    (hq : ∀ i, 1 ≤ q i) :
    IsReflexive (weightedSimplex q) ↔ ∀ i, q i ∣ 1 + ∑ j, q j

/-- Theorem 1, `(r,x)` form: for valid support data, reflexivity is equivalent
to the support LCM dividing `1+∑xᵢrᵢ`.  Expansion by `expandSupport` implements
the paper's repeated-entry vector.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 1. -/
public theorem_wanted reflexive_support_iff_lcm_dvd {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x) :
    IsReflexive (weightedSimplexList (expandSupport r x)) ↔
      weightLcm (List.ofFn r) ∣ 1 + ∑ i, x i * r i

/-- Lemma 1's two conclusions in Setup 1: reflexivity forces the support gcd
to be `1`, and the LCM of the complementary factors `sᵢ` equals the support
LCM.  `Finset.univ.gcd/lcm` encode the multiargument gcd and lcm.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Lemma 1. -/
public theorem_wanted support_gcd_and_complementary_lcm {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x))) :
    Finset.univ.gcd r = 1 ∧
      Finset.univ.lcm (setupS r) = weightLcm (List.ofFn r)

/-- The affine free sum `P *_v Q`, embedded as
`conv((P×0) ∪ (0×(Q-v)))`.  Sum-indexed coordinates are canonically
`ℝ^(n+m)` and avoid choosing an explicit equivalence with `Fin (n+m) → ℝ`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def affineFreeSum {n m : ℕ} (P : Set (Fin n → ℝ)) (Q : Set (Fin m → ℝ))
    (v : Fin m → ℝ) : Set (Sum (Fin n) (Fin m) → ℝ) :=
  convexHull ℝ
    (Set.image (fun p => Sum.elim p (fun _ => 0)) P ∪
      Set.image (fun q => Sum.elim (fun _ => 0) (q - v)) Q)

/-- The distinguished vertex `v₀=-∑qᵢeᵢ` used for the subscript-zero free sum.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public def negativeWeightVertex {n : ℕ} (q : Fin n → ℕ) : Fin n → ℝ :=
  fun i => -(q i : ℝ)

/-- Theorem 2's first sentence, the direction that holds for the weight vector alone:
if `Δ_(1,p)` and `Δ_(1,w)` are reflexive and `q = (p, (1+∑pᵢ)w)`, then `Δ_(1,q)` is
reflexive.  The geometric clause “arises as a free sum `Δ_(1,p) *_0 Δ_(1,w)`” is not
formalized, and the converse is not stated: without that clause it is false, e.g.
`p = (2)`, `w = (1)`, `q = (2,3)` has `Δ_(1,q)` reflexive (`2, 3 ∣ 6`) while `Δ_(1,p)` is
not (`2 ∤ 3`).
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem_wanted weighted_free_sum_reflexive (p w : List ℕ)
    (hp : ∀ a ∈ p, 1 ≤ a) (hw : ∀ a ∈ w, 1 ≤ a)
    (hpRef : IsReflexive (weightedSimplexList p))
    (hwRef : IsReflexive (weightedSimplexList w)) :
    IsReflexive (weightedSimplexList (p ++ w.map (fun a => (1 + p.sum) * a)))

/-- Theorem 2's second sentence: if the second polytope is IDP reflexive and
the first is IDP, their affine free sum at the distinguished negative vertex
is IDP.  Lattice points in the product are represented by pairs of integer vectors.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem_wanted affineFreeSum_idp {n m : ℕ} (q : Fin n → ℕ) (p : Fin m → ℕ)
    (hpRef : IsReflexive (weightedSimplex p)) (hpIDP : HasIDP (weightedSimplex p))
    (hqIDP : HasIDP (weightedSimplex q)) :
    HasIDP (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p))

/-- Theorem 2's third sentence: reflexivity, IDP, and `h*`-unimodality of both
weighted simplices are preserved by their subscript-zero affine free sum.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 2. -/
public theorem_wanted affineFreeSum_reflexive_idp_hStarUnimodal {n m : ℕ}
    (q : Fin n → ℕ) (p : Fin m → ℕ)
    (hqRef : IsReflexive (weightedSimplex q)) (hpRef : IsReflexive (weightedSimplex p))
    (hqIDP : HasIDP (weightedSimplex q)) (hpIDP : HasIDP (weightedSimplex p))
    (hqUni : IsHStarUnimodal (weightedSimplex q))
    (hpUni : IsHStarUnimodal (weightedSimplex p)) :
    IsReflexive (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p)) ∧
    HasIDP (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p)) ∧
    IsHStarUnimodal (affineFreeSum (weightedSimplex q) (weightedSimplex p)
      (negativeWeightVertex p))

/-- Theorem 3: for a fixed increasing positive support with some earlier entry
not dividing the last, the set of positive multiplicity vectors producing
reflexive IDP simplices is finite.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 3. -/
public theorem_wanted finite_idp_reflexive_multiplicities {d : ℕ} (r : Fin d → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hrinc : StrictMono r)
    (hndvd : ∃ j : Fin d, ∃ h : j.val + 1 < d,
      ¬r j ∣ r ⟨d - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) (by omega)⟩) :
    {x : Fin d → ℕ | (∀ i, 1 ≤ x i) ∧
      IsReflexive (weightedSimplexList (expandSupport r x)) ∧
      HasIDP (weightedSimplexList (expandSupport r x))}.Finite

/-- Theorem 4: for a reflexive positive weighted simplex, IDP is equivalent to
the paper's floor criterion.  Excluding `j` is expressed by `Finset.univ.erase j`;
all floors are natural divisions because all numerators are nonnegative.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 4. -/
public theorem_wanted idp_reflexive_floor_characterization {n : ℕ} (q : Fin n → ℕ)
    (hq : ∀ i, 1 ≤ q i) (href : IsReflexive (weightedSimplex q)) :
    HasIDP (weightedSimplex q) ↔
      ∀ j, ∀ b : ℕ, 1 ≤ b → b < q j →
        2 ≤ b * ((1 + ∑ i ∈ Finset.univ.erase j, q i) / q j) -
          ∑ i ∈ Finset.univ.erase j, b * q i / q j →
        ∃ c : ℕ, 1 ≤ c ∧ c < b ∧
          (∀ i ∈ Finset.univ.erase j,
            b * q i / q j - c * q i / q j = (b - c) * q i / q j) ∧
          c * ((1 + ∑ i ∈ Finset.univ.erase j, q i) / q j) -
            ∑ i ∈ Finset.univ.erase j, c * q i / q j = 1

/-- Corollary 1, coordinate form: an IDP reflexive weighted simplex satisfies
`1+∑ᵢ(qᵢ mod qⱼ)=qⱼ` for every coordinate, exactly `SatisfiesIDPNecessary`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public theorem_wanted idp_reflexive_implies_necessary {n : ℕ} (q : Fin n → ℕ)
    (href : IsReflexive (weightedSimplex q)) (hidp : HasIDP (weightedSimplex q)) :
    SatisfiesIDPNecessary q

/-- Corollary 1, support form: for valid `(r,x)`, IDP reflexivity implies
`1+∑ᵢxᵢ(rᵢ mod rⱼ)=rⱼ` for every support entry.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Corollary 1. -/
public theorem_wanted idp_reflexive_implies_support_necessary {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x)))
    (hidp : HasIDP (weightedSimplexList (expandSupport r x))) :
    SatisfiesSupportIDPNecessary r x

/-- Theorem 5: the explicit weighted-simplex polynomial satisfies the defining
Ehrhart power-series identity and hence is the paper's `h*`-polynomial.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 5. -/
public theorem_wanted weightedSimplex_hStar_formula (q : List ℕ) (hq : ∀ a ∈ q, 1 ≤ a) :
    IsHStarPolynomial (weightedSimplexList q) (hStarFormula q)

/-- Theorem 6: in Setup 1, the formula polynomial factors as the geometric
series `∑_{t<ℓ}z^t` times `g_r^x(z)`.  Reflexivity supplies exactness of `ℓ`
and each `sᵢ`; polynomial equality is the displayed `h*` factorization.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 6. -/
public theorem_wanted hStar_geometric_factorization {d : ℕ} (r x : Fin d → ℕ)
    (hvalid : ValidSupport r x)
    (href : IsReflexive (weightedSimplexList (expandSupport r x))) :
    hStarFormula (expandSupport r x) =
      (∑ t ∈ Finset.range (setupEll r x), Polynomial.X ^ t) * setupG r x

/-- Theorem 7's two bounds: every nonfinal multiplicity is at most
`rᵢ₊₁/rᵢ`, and if `rⱼ∤r_last`, then `x_last≤rⱼ/(r_last mod rⱼ)`.
The explicit `j.val+1<d` evidence safely names the final `Fin d` coordinate.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 7. -/
public theorem_wanted idp_reflexive_multiplicity_bounds {d : ℕ} (r x : Fin d → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r)
    (href : IsReflexive (weightedSimplexList (expandSupport r x)))
    (hidp : HasIDP (weightedSimplexList (expandSupport r x))) :
    (∀ i : Fin d, ∀ h : i.val + 1 < d,
      x i ≤ r ⟨i.val + 1, h⟩ / r i) ∧
    (∀ j : Fin d, ∀ h : j.val + 1 < d,
      let last : Fin d := ⟨d - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) (by omega)⟩
      ¬r j ∣ r last → x last ≤ r j / (r last % r j))

/-- Proposition 1: in a one-supported positive vector, IDP reflexivity forces
the sole support value to be `1`; this is the journal version's conclusion
`q=(1,…,1)` expressed at support level.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Proposition 1. -/
public theorem_wanted one_supported_idp_reflexive_support_eq_one (r x : ℕ)
    (hr : 1 ≤ r) (hx : 1 ≤ x)
    (href : IsReflexive (weightedSimplexList (List.replicate x r)))
    (hidp : HasIDP (weightedSimplexList (List.replicate x r))) : r = 1

/-- Theorem 8's iff: for two distinct increasing positive support entries and
positive multiplicities, IDP reflexivity is equivalent to the necessary condition.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 8. -/
public theorem_wanted two_supported_idp_reflexive_iff_necessary (r x : Fin 2 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    (IsReflexive (weightedSimplexList (expandSupport r x)) ∧
      HasIDP (weightedSimplexList (expandSupport r x))) ↔
      SatisfiesSupportIDPNecessary r x

/-- Theorem 8's classification: the necessary two-supported data are exactly
`(1,1+x₁)` or `(1+x₂,1+(1+x₂)x₁)`, with subscripts represented by `Fin 2`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 8. -/
public theorem_wanted two_supported_classification (r x : Fin 2 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    SatisfiesSupportIDPNecessary r x ↔
      (r 0 = 1 ∧ r 1 = 1 + x 0) ∨
      (r 0 = 1 + x 1 ∧ r 1 = 1 + (1 + x 1) * x 0)

/-- The eight support triples appearing in Theorem 9.  Cases `0` through `6`
are the paper's (i)--(vii).  Case `7` uses parameters `k,s` for (viii).
This helper only packages the printed formulas; the classification below also
states (viii)'s required equation for `x₃`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public def threeSupportFamily (case k s : ℕ) (x : Fin 3 → ℕ) : Fin 3 → ℕ :=
  match case with
  | 0 => ![1, 1 + x 0, (1 + x 0) * (1 + x 1)]
  | 1 => ![1 + x 1, 1 + x 0 * (1 + x 1),
      (1 + x 0 * (1 + x 1)) * (1 + x 1)]
  | 2 => ![(1 + x 1) * (1 + x 2),
      1 + x 0 * (1 + x 1) * (1 + x 2),
      (1 + x 0 * (1 + x 1) * (1 + x 2)) * (1 + x 1)]
  | 3 => ![1, (1 + x 0) * (1 + x 2),
      (1 + x 0) * (1 + x 1 * (1 + x 2))]
  | 4 => ![1 + (1 + x 2) * x 1,
      (1 + x 2) * (1 + x 0 * (1 + (1 + x 2) * x 1)),
      (1 + (1 + (1 + x 2) * x 1) * x 0) * (1 + (1 + x 2) * x 1)]
  | 5 => ![(1 + x 2) * (1 + (1 + x 2) * x 1),
      (1 + x 2) * (1 + x 0 * (1 + x 2) * (1 + (1 + x 2) * x 1)),
      (1 + (1 + x 2) * (1 + (1 + x 2) * x 1) * x 0) *
        (1 + (1 + x 2) * x 1)]
  | 6 => ![1 + x 2, (1 + x 2) * (1 + x 0 * (1 + x 2)),
      (1 + (1 + x 2) * x 0) * (1 + (1 + x 2) * x 1)]
  | _ => ![1 + k * x 1,
      (s * k * x 1 + s + k) * (1 + x 0 * (1 + k * x 1)),
      (1 + x 0 * (1 + k * x 1)) * (1 + x 1 * (s * k * x 1 + s + k))]

/-- Theorem 9's classification clause: every positive three-supported vector
satisfying the necessary condition has one of forms (i)--(viii).  The paper
states this direction, not a converse for arbitrary parameters; for example,
case (viii) with `x=(1,1,2), k=2, s=1` gives `r=(3,20,24)` and fails the
necessary condition.  The eighth disjunct includes `k,s≥1` and
`x₃=skx₂+s-k+1` exactly as printed.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted three_supported_classification (r x : Fin 3 → ℕ)
    (hrpos : ∀ i, 1 ≤ r i) (hxpos : ∀ i, 1 ≤ x i) (hrinc : StrictMono r) :
    SatisfiesSupportIDPNecessary r x →
      (∃ c : Fin 7, r = threeSupportFamily c.val 0 0 x) ∨
      (∃ k s : ℕ, 1 ≤ k ∧ 1 ≤ s ∧ x 2 = s * k * x 1 + s - k + 1 ∧
        r = threeSupportFamily 7 k s x)

/-- Theorem 9's final clause for cases (i)--(vii): each of the first seven
support formulas produces a reflexive IDP weighted simplex for positive `x`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted first_seven_three_supported_families_are_idp (x : Fin 3 → ℕ)
    (hxpos : ∀ i, 1 ≤ x i) (c : Fin 7) :
    IsReflexive (weightedSimplexList (expandSupport (threeSupportFamily c.val 0 0 x) x)) ∧
    HasIDP (weightedSimplexList (expandSupport (threeSupportFamily c.val 0 0 x) x))

/-- Theorem 9's final clause for case (viii): under its positive parameters,
multiplicity equation, and the theorem's ambient necessary-condition premise,
the resulting reflexive weighted simplex is not IDP.  Retaining that premise is
essential because the displayed parameter equations alone need not imply it.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 9. -/
public theorem_wanted eighth_three_supported_family_is_not_idp (x : Fin 3 → ℕ) (k s : ℕ)
    (hxpos : ∀ i, 1 ≤ x i) (hk : 1 ≤ k) (hs : 1 ≤ s)
    (hx3 : x 2 = s * k * x 1 + s - k + 1)
    (hnecessary : SatisfiesSupportIDPNecessary (threeSupportFamily 7 k s x) x) :
    IsReflexive (weightedSimplexList (expandSupport (threeSupportFamily 7 k s x) x)) ∧
    ¬HasIDP (weightedSimplexList (expandSupport (threeSupportFamily 7 k s x) x))

/-! ## Reflexive stabilizations and Theorems 10--13 -/

/-- The reflexive stabilization number is the least number of leading `1`s
that makes the resulting weighted simplex reflexive.  `sInf` directly encodes
the paper's minimum; Theorem 1 ensures the defining set is nonempty for positive
weights, rather than baking its divisibility criterion into reflexivity.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilizationNumber (q : List ℕ) : ℕ :=
  sInf {k : ℕ | IsReflexive (weightedSimplexList (List.replicate k 1 ++ q))}

/-- The first reflexive stabilization `rs(q)=(1^{rsn(q)},q)`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilization (q : List ℕ) : List ℕ :=
  List.replicate (reflexiveStabilizationNumber q) 1 ++ q

/-- The `m`th reflexive stabilization
`rs(q,m)=(1^{rsn(q)+(m-1)lcm(q)},q)`, with natural subtraction matching `m≥1`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public noncomputable def reflexiveStabilizationAt (q : List ℕ) (m : ℕ) : List ℕ :=
  List.replicate (reflexiveStabilizationNumber q + (m - 1) * weightLcm q) 1 ++ q

/-- The list version `ℓ(q)=(1+∑qᵢ)/lcm(q)`, used for stabilized vectors in
Theorem 12.  Natural division is exact when that vector is reflexive.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public def listEll (q : List ℕ) : ℕ := (1 + q.sum) / weightLcm q

/-- Theorem 10: if `q` is nonempty and every original weight is at least `2`, every
stabilization with `m≥2` fails IDP.  Nonemptiness is the paper's `q ∈ ℤ^n_{≥1}`, `n ≥ 1`:
for `q = []`, `rs([],2) = [1]` gives the interval `[-1,1]`, which has IDP.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 10. -/
public theorem_wanted higher_reflexive_stabilizations_not_idp (q : List ℕ)
    (hne : q ≠ []) (hq : ∀ a ∈ q, 2 ≤ a) (m : ℕ) (hm : 2 ≤ m) :
    ¬HasIDP (weightedSimplexList (reflexiveStabilizationAt q m))

/-- Theorem 11: eventually the stabilized simplex is not `h*`-unimodal and
every coefficient of its explicit (hence, by Theorem 5, Ehrhart) `h*` formula
is `1` or `2`.  `∀ᶠ m in atTop` formalizes “for sufficiently large `m`”.
The hypothesis `lcm(q) ≥ 3` is the journal version's (the arXiv version omits it, and then
`q = [2]` is a counterexample: its stabilizations have `h*`-vector `(1,…,1,2,1,…,1)`, which is
unimodal).
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 11. -/
public theorem_wanted stabilization_eventually_not_unimodal_coefficients_one_or_two
    (q : List ℕ) (hq : ∀ a ∈ q, 2 ≤ a) (hlcm : 3 ≤ weightLcm q) :
    ∀ᶠ m in atTop,
      ¬IsHStarUnimodal (weightedSimplexList (reflexiveStabilizationAt q m)) ∧
      ∀ k : ℕ, k ≤ (hStarFormula (reflexiveStabilizationAt q m)).natDegree →
        (hStarFormula (reflexiveStabilizationAt q m)).coeff k = 1 ∨
          (hStarFormula (reflexiveStabilizationAt q m)).coeff k = 2

/-- Theorem 12's weight equality.  The hypotheses `rsn(q)=1` and `ℓ(rs(q))=1`
are stated literally.  The paper's gloss `1+∑qᵢ=lcm(q)-1` is equivalent to
`2+∑qᵢ=lcm(q)`, the numerator equation for the one-leading-`1` stabilization;
no correction to the printed statement is needed.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public theorem_wanted stabilization_weightStatistic_eq (q : List ℕ)
    (hrsn : reflexiveStabilizationNumber q = 1)
    (hell : listEll (reflexiveStabilization q) = 1) :
    ∀ b : ℕ, b ≤ q.sum →
      weightStatistic q b = weightStatistic (reflexiveStabilization q) b

/-- Theorem 12's consequence for `h*`: the first stabilization adds precisely
the monomial `z^(n+1)`, where `n=q.length`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 12. -/
public theorem_wanted stabilization_hStar_add_monomial (q : List ℕ)
    (hrsn : reflexiveStabilizationNumber q = 1)
    (hell : listEll (reflexiveStabilization q) = 1) :
    hStarFormula (reflexiveStabilization q) =
      hStarFormula q + Polynomial.X ^ (q.length + 1)

/-- A homogenized lattice point `(height,w)` belongs to the cone over `P` when
`w` is a lattice point of the corresponding height dilate.  This is exactly
the height-slice encoding used earlier for IDP.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def IsConeLatticePoint {n : ℕ} (P : Set (Fin n → ℝ))
    (a : ℕ × (Fin n → ℤ)) : Prop := IsLatticePoint (polytopeDilate a.1 P) a.2

/-- An irreducible nonzero cone lattice point: every decomposition into two
cone lattice points has a zero summand.  The task permits this irreducible-
elements presentation of the minimal monoid generating set called a Hilbert basis.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def IsHilbertBasisElement {n : ℕ} (P : Set (Fin n → ℝ))
    (a : ℕ × (Fin n → ℤ)) : Prop :=
  IsConeLatticePoint P a ∧ a ≠ 0 ∧
    ∀ b c : ℕ × (Fin n → ℤ), IsConeLatticePoint P b → IsConeLatticePoint P c →
      a = b + c → b = 0 ∨ c = 0

/-- The Hilbert basis is represented as the set of irreducible nonzero lattice
points of the cone, an equivalent minimal-generator formulation for this positive monoid.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def hilbertBasis {n : ℕ} (P : Set (Fin n → ℝ)) : Set (ℕ × (Fin n → ℤ)) :=
  {a | IsHilbertBasisElement P a}

/-- The weight vector `q(n)=(1^{2n-1},3n,10n,15n)` from Theorem 13, directly
indexed by `Fin (2n+2)`.  The first branch has `2n-1` coordinates.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def almostIDPWeights (n : ℕ) : Fin (2 * n + 2) → ℕ := fun i =>
  if i.val < 2 * n - 1 then 1
  else if i.val = 2 * n - 1 then 3 * n
  else if i.val = 2 * n then 10 * n
  else 15 * n

/-- The opening clause of Theorem 13: for `n≥1`, the vector
`(1^{2n-1},3n,10n,15n)` is exactly the first reflexive stabilization of
`(3n,10n,15n)`.  `List.ofFn` converts the direct finite-index presentation to
the list presentation used by `reflexiveStabilization`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDPWeights_eq_reflexiveStabilization (n : ℕ) (hn : 1 ≤ n) :
    List.ofFn (almostIDPWeights n) =
      reflexiveStabilization [3 * n, 10 * n, 15 * n]

/-- The homogenized vertex set `V(n)`: the negative weight vertex and every
standard basis vertex, all at height `1`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def homogenizedWeightedVertices {n : ℕ} (q : Fin n → ℕ) :
    Set (ℕ × (Fin n → ℤ)) :=
  {(1, fun i => -(q i : ℤ))} ∪ Set.range (fun i : Fin n => (1, Pi.single i (1 : ℤ)))

/-- The nine exceptional columns in Theorem 13's matrix.  Coordinates before
the last three are zero; the last triples are exactly the nine printed columns,
and heights are `1` for columns `0`--`6` and `2` for columns `7`,`8`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def exceptionalHilbertColumn (n : ℕ) (j : Fin 9) :
    ℕ × (Fin (2 * n + 2) → ℤ) :=
  let triples : Fin 9 → Fin 3 → ℤ := ![
    ![0, 0, 0], ![0, 0, -1], ![0, -1, -1], ![0, -1, -2], ![0, -2, -3],
    ![0, -3, -5], ![-1, -4, -6], ![-2, -7, -10], ![-3, -10, -15]]
  (if j.val < 7 then 1 else 2, fun i =>
    if i.val < 2 * n - 1 then 0
    else if _h0 : i.val = 2 * n - 1 then triples j 0
    else if _h1 : i.val = 2 * n then triples j 1
    else triples j 2)

/-- Theorem 13's Hilbert-basis description: it is exactly the homogenized
vertices together with the nine displayed exceptional columns.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_hilbertBasis (n : ℕ) (hn : 1 ≤ n) :
    hilbertBasis (weightedSimplex (almostIDPWeights n)) =
      homogenizedWeightedVertices (almostIDPWeights n) ∪
        Set.range (exceptionalHilbertColumn n)

/-- Theorem 13's height consequence: among the Hilbert basis, exactly two
elements have height greater than `1`, and both have height exactly `2`.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_exactly_two_height_two (n : ℕ) (hn : 1 ≤ n) :
    Set.ncard {a ∈ hilbertBasis (weightedSimplex (almostIDPWeights n)) | 1 < a.1} = 2 ∧
    ∀ a ∈ hilbertBasis (weightedSimplex (almostIDPWeights n)), 1 < a.1 → a.1 = 2

/-- The even geometric factor `1+z²+⋯+z^(2n-2)` used in Theorem 13.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public noncomputable def evenGeometricFactor (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range n, Polynomial.X ^ (2 * k)

/-- The quartic factor `1+7z+14z²+7z³+z⁴` from Theorem 13.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public noncomputable def almostIDPQuartic : Polynomial ℤ :=
  1 + 7 * Polynomial.X + 14 * Polynomial.X ^ 2 +
    7 * Polynomial.X ^ 3 + Polynomial.X ^ 4

/-- The exact coefficient vector represented by the paper's ellipsis:
`(1,7,15,14)`, followed by `n-2` copies of `(16,14)`, then `(15,7,1)`.
For `n=2` the repeated middle block is empty.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public def almostIDPCoefficientVector (n : ℕ) : List ℤ :=
  [1, 7, 15, 14] ++ (List.replicate (n - 2) [16, 14]).flatten ++ [15, 7, 1]

/-- Theorem 13's `h*` factorization for `n≥2`: the product of the displayed even
geometric series and quartic satisfies the Ehrhart-series identity of
`Δ_(1,q(n))`, i.e. it is the `h*`-polynomial.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_hStar_factorization (n : ℕ) (hn : 2 ≤ n) :
    IsHStarPolynomial (weightedSimplex (almostIDPWeights n))
      (evenGeometricFactor n * almostIDPQuartic)

/-- Theorem 13's coefficient-vector clause for the product above, with the ellipsis made
exact by `almostIDPCoefficientVector`.  `List.ofFn` lists coefficients from degree `0`
through degree `2n+2`, the full displayed vector.
Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article
A60, Theorem 13. -/
public theorem_wanted almostIDP_hStar_coefficients (n : ℕ) (hn : 2 ≤ n) :
    List.ofFn (fun k : Fin (2 * n + 3) =>
      (evenGeometricFactor n * almostIDPQuartic).coeff k.val) =
      almostIDPCoefficientVector n

/-- Example: `(1^2, 3^1)` expands to `(1, 1, 3)`.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2 (notation `(r_1^{x_1}, …, r_d^{x_d})`). -/
public theorem expandSupport_example : expandSupport ![1, 3] ![2, 1] = [1, 1, 3] := by
  decide

/-- Example: `lcm(2, 2, 3) = 6`.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2. -/
public theorem weightLcm_example : weightLcm [2, 2, 3] = 6 := by
  decide

/-- The paper's example after Theorem 5: for `q = (2, 2, 3)` the formula gives
`1 + 2z + 4z² + z³`.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
example after Theorem 5. -/
public theorem hStarFormula_two_two_three :
    hStarFormula [2, 2, 3] =
      1 + 2 * Polynomial.X + 4 * Polynomial.X ^ 2 + Polynomial.X ^ 3 := by
  have h : ∀ b, weightStatistic [2, 2, 3] b = b - (2 * b / 8 + (2 * b / 8 + 3 * b / 8)) := by
    intro b; simp [weightStatistic]
  rw [hStarFormula, show ([2, 2, 3] : List ℕ).sum + 1 = 8 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h]
  norm_num
  ring

/-- The paper's example after Theorem 6: for `q = (1^7, 3^4, 5^5)`, `ℓ = 3`.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
example after Theorem 6. -/
public theorem setupEll_example : setupEll ![1, 3, 5] ![7, 4, 5] = 3 := by
  decide

/-- The dilate by `1` is the polytope itself.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Section 2.3 (dilates `tP`). -/
public theorem polytopeDilate_one {ι : Type*} (P : Set (ι → ℝ)) : polytopeDilate 1 P = P := by
  ext x
  simp [polytopeDilate]

/-- For `n = 1` the weights of Theorem 13 are `(1, 3, 10, 15)`.

Source: Benjamin Braun, Robert Davis, Derek Hanely, Morgan Lane, and Liam Solus, *The Integer
Decomposition Property and Weighted Projective Space Simplices*, INTEGERS 24 (2024), Article A60,
Theorem 13. -/
public theorem almostIDPWeights_one : List.ofFn (almostIDPWeights 1) = [1, 3, 10, 15] := by
  decide

end

end MetaMathlibExt

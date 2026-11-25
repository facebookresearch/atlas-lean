/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedPoincareCoefficients

/-!
# Finite support of multigraded Poincaré coefficients

This file proves that the raw edge-6 Poincaré coefficient function has
finite support once the underlying multigraded free resolution has finite
homogeneous bases in each homological degree and terminates above a
supplied homological bound.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact line 876. That line states the Hilbert syzygy consequence: over a
polynomial ring, the Poincaré series of every finitely generated module
is a polynomial. For the edge-6 raw coefficient function, polynomiality
is exactly finite support on homological degree times multidegree.

Conditional finite-resolution bridge, not the full Hilbert syzygy
theorem: the two hypotheses describe the terms of an already-supplied
finite-rank terminating resolution — every homogeneous basis index type
is finite, and those types are empty above the bound. The hypotheses say
nothing about supports, Betti numbers, or Poincaré coefficients, so
finite support is genuinely derived from the resolution geometry:
outside the finite set of actual homogeneous basis degrees, the degree
piece is the span of the empty set, the component complex is zero there,
and the Betti coefficient vanishes. In particular, nothing here
constructs such a resolution for every finitely generated module over
`MvPolynomial`, proves the classical bound by the number of variables,
or assumes finite coefficient support, eventual Betti vanishing, a
`Finsupp` or `AddMonoidAlgebra` value, minimality, or comparison data.
That existence step is a later Hilbert-syzygy edge.

Main results:

* `MetaMathlibExt.multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution`:
  the raw coefficient function has finite support under the two
  structural resolution hypotheses above.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

/-- Recorded homogeneous degree of a term basis index. The
`MultigradedFreeModule` instance on each resolution term is the local
`Module.compHom` instance via `MvPolynomial.C`, so it is installed inside
the body; callers never supply instances. -/
private noncomputable def termDeg {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) (j : ι i) : Fin n →₀ Int :=
  letI : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  (res.termFree i).degree j

/-- If no basis index at term `i` has degree `α`, the base-changed degree
piece at `(i, α)` is the span of the empty set, hence bottom. -/
private lemma pieceEqBotOfNoDegree {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (i : ℕ) (α : Fin n →₀ Int)
    (hAll : ∀ j : ι i, termDeg res i j ≠ α) :
    baseChangedDegreePiece targetGraded resolution ι res i α = ⊥ := by
  unfold baseChangedDegreePiece
  rw [Submodule.span_eq_bot]
  intro y hy
  obtain ⟨j, hjDeg, rfl⟩ := hy
  exact absurd hjDeg (hAll j)

/-- If no basis index at term `i` has degree `α`, the `i`-th object of the
`α` component complex is a subsingleton: the certified inclusion is
injective and its range is the bottom degree piece. -/
private lemma compObjSubsingletonOfNoDegree {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (i : ℕ) (α : Fin n →₀ Int)
    (hAll : ∀ j : ι i, termDeg res i j ≠ α) :
    Subsingleton ↥((data.comp α).X i) := by
  have hPiece : baseChangedDegreePiece targetGraded resolution ι res i α = ⊥ :=
    pieceEqBotOfNoDegree (res := res) i α hAll
  have hInj : Function.Injective
      ⇑(ModuleCat.Hom.hom ((data.incl α).f i)) :=
    data.incl_injective α i
  have hRan : LinearMap.range (ModuleCat.Hom.hom ((data.incl α).f i)) =
      baseChangedDegreePiece targetGraded resolution ι res i α :=
    data.range_eq α i
  rw [hPiece] at hRan
  refine ⟨fun a b => hInj ?_⟩
  have ha : (ModuleCat.Hom.hom ((data.incl α).f i)) a = 0 := by
    have hmem : (ModuleCat.Hom.hom ((data.incl α).f i)) a ∈
        LinearMap.range (ModuleCat.Hom.hom ((data.incl α).f i)) :=
      LinearMap.mem_range_self _ a
    rw [hRan] at hmem
    simpa using hmem
  have hb : (ModuleCat.Hom.hom ((data.incl α).f i)) b = 0 := by
    have hmem : (ModuleCat.Hom.hom ((data.incl α).f i)) b ∈
        LinearMap.range (ModuleCat.Hom.hom ((data.incl α).f i)) :=
      LinearMap.mem_range_self _ b
    rw [hRan] at hmem
    simpa using hmem
  rw [ha, hb]

/-- If no basis index at term `i` has degree `α`, the Betti coefficient at
`(α, i)` is zero: the component object is a zero object, so its homology
is zero. -/
private lemma bettiEqZeroOfNoDegree {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (α : Fin n →₀ Int) (i : ℕ)
    (hAll : ∀ j : ι i, termDeg res i j ≠ α) :
    multigradedBettiNumber data α i = 0 := by
  have _hSubX : Subsingleton ↥((data.comp α).X i) :=
    compObjSubsingletonOfNoDegree data i α hAll
  have _hHas : HomologicalComplex.HasHomology (data.comp α) i :=
    data.hasHom α i
  have _hFin : Module.Finite K ↥(HomologicalComplex.homology (data.comp α) i) :=
    data.finiteDim α i
  have hIsZeroX : CategoryTheory.Limits.IsZero ((data.comp α).X i) :=
    ModuleCat.isZero_of_subsingleton _
  have hExact : (data.comp α).ExactAt i :=
    HomologicalComplex.ExactAt.of_isZero hIsZeroX
  have hZeroH : CategoryTheory.Limits.IsZero
      (HomologicalComplex.homology (data.comp α) i) :=
    hExact.isZero_homology
  have _hSubH : Subsingleton ↥(HomologicalComplex.homology (data.comp α) i) :=
    ModuleCat.isZero_iff_subsingleton.mp hZeroH
  unfold multigradedBettiNumber
  exact Module.finrank_zero_of_subsingleton

/-- **Finite support of the multigraded Poincaré coefficients.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded $R$-module, and let $D$ be base-change data
for a multigraded free resolution $F_\bullet$ of $M$ in which $F_i$ has a homogeneous basis
indexed by $\iota_i$. Suppose every $\iota_i$ is finite and, for some $b \in \mathbb{N}$,
$\iota_i$ is empty for every $i > b$. Then the multigraded Poincaré coefficient family of $D$ is
nonzero at only finitely many $(i, \alpha) \in \mathbb{N} \times \mathbb{Z}^n$.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact line 876. This is the conditional finite-resolution bridge behind
that line, not the full Hilbert syzygy existence theorem: it assumes the
finite terminating resolution and derives finite coefficient support,
without assuming finite support, eventual Betti vanishing, or a
polynomial realization, and without constructing the resolution. -/
public theorem multigradedPoincareCoefficients_hasFiniteSupport_of_finiteResolution
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (bound : ℕ)
    (finiteBasis : ∀ i, Finite (ι i))
    (emptyAbove : ∀ i, bound < i → IsEmpty (ι i)) :
    Function.HasFiniteSupport (multigradedPoincareCoefficients data) := by
  classical
  have key : ∀ (i : ℕ) (α : Fin n →₀ Int),
      multigradedPoincareCoefficients data (i, α) ≠ 0 →
      i ≤ bound ∧ ∃ j : ι i, termDeg res i j = α := by
    intro i α hCoeff
    have hLe : i ≤ bound := by
      by_contra hNot
      have hLt : bound < i := lt_of_not_ge hNot
      have _hEmpty : IsEmpty (ι i) := emptyAbove i hLt
      have hAll : ∀ j : ι i, termDeg res i j ≠ α := by
        intro j
        exact False.elim (IsEmpty.false j)
      exact hCoeff (bettiEqZeroOfNoDegree data α i hAll)
    refine ⟨hLe, ?_⟩
    by_contra hNone
    push Not at hNone
    exact hCoeff (bettiEqZeroOfNoDegree data α i hNone)
  have hUnion : (⋃ i ∈ Set.Iic bound,
      Set.range (fun j : ι i => (i, termDeg res i j))).Finite := by
    apply Set.Finite.biUnion (Set.finite_Iic bound)
    intro i _
    have _hFin : Finite (ι i) := finiteBasis i
    exact Set.finite_range _
  apply hUnion.subset
  intro p hp
  have hpSupp : multigradedPoincareCoefficients data p ≠ 0 :=
    Function.mem_support.mp hp
  obtain ⟨hLe, j, hj⟩ := key p.1 p.2 hpSupp
  have hMem : (p.1, termDeg res p.1 j) ∈
      ⋃ i ∈ Set.Iic bound,
        Set.range (fun j : ι i => (i, termDeg res i j)) := by
    rw [Set.mem_iUnion]
    refine ⟨p.1, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hLe, Set.mem_range_self j⟩
  rw [hj] at hMem
  simpa using hMem

end MetaMathlibExt

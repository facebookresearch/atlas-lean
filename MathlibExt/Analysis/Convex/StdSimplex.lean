/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `c3bae57ddba11aa34b3cbc61270f587aa4c40152`.

Introduced by Meta Muse; principal content by Tsutomu Okano (@toskua),
as credited in the upstream author line; ported with attribution.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Fin.SuccPred

/-!
# Generic finite-distribution operations on `Convexity.StdSimplex`

This module equips `Convexity.StdSimplex R X` with reusable finite-distribution
operations, domain-neutral and with transparent scalar generality
`Semiring R`, `PartialOrder R`, `IsStrictOrderedRing R`:

* `iConvexComb` is the canonical stochastic composition, with
  `((w.iConvexComb f).weights y = ∑ x, w.weights x * (f x).weights y)`.
* `StdSimplex.single` is the Dirac / pure.
* `StdSimplex.map` is the functorial pushforward.
* `StdSimplex.sigma` is the dependent-pair distribution, implemented
  directly through `iConvexComb` and `map`, with
  `(sigma w f).weights p = w.weights p.1 * (f p.1).weights p.2`.
* `StdSimplex.prod` is the independent product, defined compositionally from
  `sigma` and `Equiv.sigmaEquivProd`, not by a third duplicated normalization proof.
* Nonzero coordinates use `Finsupp.support` directly
  (`p.weights.support`, characterized by `Finsupp.mem_support_iff`); no
  wrapper is provided.
* `face_factor_succAbove` factors a point with a zero coordinate through the
  corresponding face; `fin1_pos` is the dimension-zero positivity base case.

Proofs use the canonical `iConvexComb` definition and `Finsupp` weight lemmas.
-/

@[expose] public section

namespace Convexity.StdSimplex

variable {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
variable {X Y : Type*}

/-- Finsupp characteristic formula for canonical stochastic composition: weights
of the mixture are the `w`-weighted sum of the kernel weights. -/
@[simp]
theorem weights_iConvexComb_eq_sum (w : StdSimplex R X)
    (f : X → StdSimplex R Y) :
    (w.iConvexComb f).weights
      = w.weights.sum (fun x r => r • (f x).weights) := by
  simp [iConvexComb, Finsupp.sum_mapDomain_index, add_smul]

/-- Coordinate formula for canonical stochastic composition: weight at output
`y` sums the `w`-weighted kernel weights over the input index `x`. -/
-- `nolint simpNF`: the Finsupp-level `weights_iConvexComb_eq_sum` above is
-- deliberately also `simp`; both levels are part of the simp API.
@[simp, nolint simpNF]
theorem weights_iConvexComb_apply [Fintype X] (w : StdSimplex R X)
    (f : X → StdSimplex R Y) (y : Y) :
    (w.iConvexComb f).weights y
      = ∑ x : X, w.weights x * (f x).weights y := by
  classical
  have hsum := weights_iConvexComb_eq_sum w f
  calc (w.iConvexComb f).weights y
      = (w.weights.sum (fun x r => r • (f x).weights)) y := by rw [hsum]
    _ = w.weights.sum (fun x r => (r • (f x).weights) y) := by
        rw [Finsupp.sum_apply]
    _ = w.weights.sum (fun x r => r * (f x).weights y) := by
        simp only [Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ x : X, w.weights x * (f x).weights y := by
        rw [Finsupp.sum_fintype _ _ (fun x => by simp)]

section Sigma

variable {Y' : X → Type*}

/-- Dependent-pair distribution over `Sigma Y'`: draw `x` from `w`, then draw from
`f x` and pair the result with `x`. -/
noncomputable def sigma (w : StdSimplex R X)
    (f : (x : X) → StdSimplex R (Y' x)) :
    StdSimplex R (Sigma Y') :=
  w.iConvexComb (fun x => (f x).map (Sigma.mk x))

/-- Coordinate formula for `sigma`: weight at `p` factors as the input weight at
`p.1` times the fiber weight at `p.2`. -/
@[simp]
theorem sigma_apply (w : StdSimplex R X)
    (f : (x : X) → StdSimplex R (Y' x)) (p : Sigma Y') :
    (sigma w f).weights p = w.weights p.1 * (f p.1).weights p.2 := by
  obtain ⟨x, y⟩ := p
  classical
  have hweights : (sigma w f).weights
      = w.weights.sum
        (fun x' r => r • (((f x').map (Sigma.mk x')).weights)) := by
    simp only [sigma]
    exact weights_iConvexComb_eq_sum w _
  have happly : (sigma w f).weights (⟨x, y⟩ : Sigma Y')
      = w.weights.sum
        (fun x' r =>
          (r • (((f x').map (Sigma.mk x')).weights)) (⟨x, y⟩ : Sigma Y')) := by
    rw [hweights, Finsupp.sum_apply]
  have hsmul : (fun x' r =>
        (r • (((f x').map (Sigma.mk x')).weights)) (⟨x, y⟩ : Sigma Y'))
      = (fun x' r => r * (((f x').map (Sigma.mk x')).weights) (⟨x, y⟩ : Sigma Y')) := by
    funext x' r
    rw [Finsupp.smul_apply, smul_eq_mul]
  rw [happly, hsmul]
  have hfin : w.weights.sum
        (fun x' r => r * (((f x').map (Sigma.mk x')).weights) (⟨x, y⟩ : Sigma Y'))
      = w.weights.support.sum
        (fun x' => w.weights x' * (((f x').map (Sigma.mk x')).weights) (⟨x, y⟩ : Sigma Y')) :=
    rfl
  rw [hfin]
  rw [Finset.sum_eq_single x]
  · have hinj : Function.Injective (Sigma.mk x : Y' x → Sigma Y') := by
      intro y1 y2 h
      simpa using h
    have hmain : (((f x).map (Sigma.mk x)).weights) (⟨x, y⟩ : Sigma Y')
        = (f x).weights y := by
      rw [weights_map]
      have h := Finsupp.mapDomain_apply_of_injective hinj (f x).weights y
      simpa using h
    rw [hmain]
  · intro x' _ hx'
    have hmem : (⟨x, y⟩ : Sigma Y') ∉ Set.range (Sigma.mk x' : Y' x' → Sigma Y') := by
      rintro ⟨y', h⟩
      have hfst : x' = x := by
        have hfst := congrArg Sigma.fst h
        simpa using hfst
      exact hx' hfst
    have hzero : ((((f x').map (Sigma.mk x')).weights) (⟨x, y⟩ : Sigma Y')) = 0 := by
      rw [weights_map]
      exact Finsupp.mapDomain_of_notMem_range _ _ hmem
    rw [hzero, mul_zero]
  · intro hx
    rw [Finsupp.notMem_support_iff.mp hx, zero_mul]

end Sigma

/-- Independent product distribution on `X × Y`: `sigma` with constant family,
transported along `Equiv.sigmaEquivProd`. -/
noncomputable def prod (p : StdSimplex R X) (q : StdSimplex R Y) :
    StdSimplex R (X × Y) :=
  (sigma p (fun _ => q)).map (Equiv.sigmaEquivProd X Y)

/-- Coordinate formula for `prod`: weight at `(x, y)` is the product of the
marginal weights at `x` and `y`. -/
@[simp]
theorem prod_apply (p : StdSimplex R X)
    (q : StdSimplex R Y) (x : X) (y : Y) :
    (prod p q).weights (x, y) = p.weights x * q.weights y := by
  classical
  have hsymm : (Equiv.sigmaEquivProd X Y).symm (x, y) = (⟨x, y⟩ : Sigma fun _ : X => Y) :=
    rfl
  calc (prod p q).weights (x, y)
      = ((sigma p (fun _ => q)).weights.mapDomain
          (Equiv.sigmaEquivProd X Y)) (x, y) := by rw [prod, weights_map]
    _ = (sigma p (fun _ => q)).weights
          ((Equiv.sigmaEquivProd X Y).symm (x, y)) := by
        rw [Finsupp.mapDomain_equiv_apply]
    _ = (sigma p (fun _ => q)).weights (⟨x, y⟩ : Sigma fun _ : X => Y) := by
        rw [hsymm]
    _ = p.weights x * q.weights y := by
        rw [sigma_apply]

section MapSupport

/-- Coordinate fiber-sum formula for `map`: the weight of `q.map f` at `j`
is the sum of the weights of `q` over the fiber `f ⁻¹ {j}`. -/
theorem weights_map_apply [Fintype X] [DecidableEq Y] (q : StdSimplex R X)
    (f : X → Y) (j : Y) :
    (q.map f).weights j
      = ∑ i ∈ Finset.univ.filter (fun i => f i = j), q.weights i := by
  classical
  rw [weights_map, Finsupp.mapDomain_fintype, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_filter]

/-- Injective coordinate maps give injective simplex maps. -/
theorem map_injective {f : X → Y} (hf : Function.Injective f) :
    Function.Injective (map (R := R) f) := by
  intro a b hab
  have h : a.weights.mapDomain f = b.weights.mapDomain f := by
    have hcongr := congrArg StdSimplex.weights hab
    simpa [weights_map] using hcongr
  have hweights : a.weights = b.weights := Finsupp.mapDomain_injective hf h
  exact weights_inj.mp hweights

/-- Surjective coordinate maps preserve strict positivity: the image of a
strictly positive point is strictly positive at every output coordinate. -/
theorem map_surjective_pos {k n : ℕ} {f : Fin k → Fin (n + 1)}
    (hf : Function.Surjective f)
    {q : StdSimplex R (Fin k)} (hq : ∀ i, 0 < q.weights i)
    (j : Fin (n + 1)) :
    0 < (q.map f).weights j := by
  classical
  rw [weights_map_apply]
  apply Finset.sum_pos
  · intro x _
    exact hq x
  · obtain ⟨x₀, hx₀⟩ := hf j
    exact ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ x₀, hx₀⟩⟩

/-- Every point of `StdSimplex ℝ (Fin (n + 1))` factors through its support by a
strictly positive point. `k` is the support cardinality and `f` enumerates
the support. -/
theorem exists_strictly_positive_preimage {n : ℕ}
    (p : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (k : ℕ) (f : Fin k → Fin (n + 1)),
      Function.Injective f ∧
        ∃ q : StdSimplex ℝ (Fin k), (∀ i, 0 < q.weights i) ∧ q.map f = p := by
  classical
  let s : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => p.weights i ≠ 0)
  have hs_mem : ∀ i : Fin (n + 1), i ∈ s ↔ p.weights i ≠ 0 := by
    intro i
    simp [s]
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ i : Fin (n + 1), p.weights i = 0 := by
      intro i
      by_contra hi
      have hi_mem : i ∈ s := by simp [s, hi]
      rw [h] at hi_mem
      exact Finset.notMem_empty i hi_mem
    have hsum : (∑ i : Fin (n + 1), p.weights i) = 0 :=
      Finset.sum_eq_zero (fun i _ => hall i)
    rw [total_of_fintype] at hsum
    exact one_ne_zero hsum
  let e : Fin s.card ≃ s := (Finset.equivFin s).symm
  let f : Fin s.card → Fin (n + 1) := fun i => (e i).val
  have hf : Function.Injective f := by
    intro a b hab
    have hsub : e a = e b := Subtype.val_injective hab
    exact e.injective hsub
  have hrange : Set.range f = ↑s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hy
      have hmem : y ∈ s := hy
      refine ⟨e.symm ⟨y, hmem⟩, ?_⟩
      simp [f, e]
  have hmem_range : p ∈ Set.range (map f) := by
    rw [mem_range_map_iff]
    intro y hy
    have hy_not_mem : y ∉ s := by
      intro hmem
      have : y ∈ (↑s : Set (Fin (n + 1))) := hmem
      rw [← hrange] at this
      exact hy this
    have : ¬ (p.weights y ≠ 0) := by
      intro hne
      exact hy_not_mem ((hs_mem y).mpr hne)
    exact of_not_not this
  obtain ⟨q, hq⟩ := hmem_range
  refine ⟨s.card, f, hf, q, ?_, hq⟩
  intro i
  have hq_nonneg : 0 ≤ q.weights i := weights_nonneg i
  have hne : q.weights i ≠ 0 := by
    intro hzero
    have hfi_mem : f i ∈ s := (e i).property
    have hfi_ne : p.weights (f i) ≠ 0 := (hs_mem (f i)).mp hfi_mem
    have hmap_eq : (q.map f).weights (f i) = q.weights i := by
      rw [weights_map]
      exact Finsupp.mapDomain_apply_of_injective hf (q.weights) i
    have hp_eq : p.weights (f i) = q.weights i := by
      have hcongr : (q.map f).weights = p.weights := by rw [hq]
      rw [hcongr] at hmap_eq
      exact hmap_eq.symm ▸ rfl
    rw [hzero] at hp_eq
    exact hfi_ne hp_eq
  exact lt_of_le_of_ne hq_nonneg (Ne.symm hne)

/-- The interior preimage above is unique for a fixed injective face. -/
theorem unique_preimage_of_injective {n k : ℕ} {f : Fin k → Fin (n + 1)}
    (hf : Function.Injective f) (p : StdSimplex ℝ (Fin (n + 1)))
    {q₁ q₂ : StdSimplex ℝ (Fin k)}
    (h₁ : q₁.map f = p) (h₂ : q₂.map f = p) :
    q₁ = q₂ := by
  have hmap_inj : Function.Injective (map (R := ℝ) f) := map_injective hf
  exact hmap_inj (by rw [h₁, h₂])

/-- A strictly positive factorization determines the face range as the
support: the only coordinates where `p` is nonzero are those in `range f`. -/
theorem range_eq_support_of_strictly_positive {n k : ℕ}
    {f : Fin k → Fin (n + 1)} (hf : Function.Injective f)
    {q : StdSimplex ℝ (Fin k)} (hq_pos : ∀ i, 0 < q.weights i)
    {p : StdSimplex ℝ (Fin (n + 1))} (hmap : q.map f = p) :
    Set.range f = {i | p.weights i ≠ 0} := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    have hqi : q.weights i ≠ 0 := ne_of_gt (hq_pos i)
    have hmap_eq : (q.map f).weights (f i) = q.weights i := by
      rw [weights_map]
      exact Finsupp.mapDomain_apply_of_injective hf _ _
    have hp_eq : p.weights (f i) = q.weights i := by
      have hcongr : (q.map f).weights = p.weights := by rw [hmap]
      rw [hcongr] at hmap_eq
      exact hmap_eq.symm ▸ rfl
    change p.weights (f i) ≠ 0
    rw [hp_eq]
    exact hqi
  · intro hy
    have hy_ne : p.weights y ≠ 0 := hy
    by_contra hy_not
    have hmem : p ∈ Set.range (map f) := ⟨q, hmap⟩
    have hzero : p.weights y = 0 := (mem_range_map_iff f p).mp hmem y hy_not
    exact hy_ne hzero

/-- Support of a general mapped strictly positive point is the coordinate
range: for arbitrary finite `f` and strictly positive `q`, the nonzero
coordinates of `q.map f` are exactly `Set.range f`. -/
theorem range_eq_support_of_map_strictly_positive {n k : ℕ}
    {f : Fin k → Fin (n + 1)}
    {q : StdSimplex ℝ (Fin k)} (hq_pos : ∀ i, 0 < q.weights i) :
    Set.range f = {i | (q.map f).weights i ≠ 0} := by
  classical
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    change (q.map f).weights (f i) ≠ 0
    rw [weights_map_apply]
    apply ne_of_gt
    apply Finset.sum_pos
    · intro x _
      exact hq_pos x
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  · intro hy
    have hy_ne : (q.map f).weights y ≠ 0 := hy
    by_contra hy_not
    have hmem : q.map f ∈ Set.range (map f) := ⟨q, rfl⟩
    have hzero : (q.map f).weights y = 0 :=
      (mem_range_map_iff f _).mp hmem y hy_not
    exact hy_ne hzero

/-- Base case: the unique point of the 0-simplex is strictly positive. -/
theorem fin1_pos (p : StdSimplex ℝ (Fin 1)) (j : Fin 1) :
    0 < p.weights j := by
  have : Subsingleton (Fin 1) :=
    ⟨fun a b => Fin.ext (by have ha := a.isLt; have hb := b.isLt; omega)⟩
  have h : p.weights j = 1 := weights_apply_eq_one p j
  rw [h]
  norm_num

/-- Single zero coordinate factors through the corresponding face:
if `p.weights j = 0` then `p` lies in the range of
`StdSimplex.map (Fin.succAbove j)`.
Direct consequence of `Convexity.StdSimplex.mem_range_map_iff`, via the
`Fin.exists_succAbove_eq_iff` characterization of the complement. -/
theorem face_factor_succAbove {n : ℕ}
    (p : StdSimplex ℝ (Fin (n + 2))) (j : Fin (n + 2))
    (hj : p.weights j = 0) :
    ∃ q : StdSimplex ℝ (Fin (n + 1)),
      StdSimplex.map (Fin.succAbove j) q = p := by
  have hmem : p ∈ Set.range (StdSimplex.map (Fin.succAbove j)) := by
    rw [mem_range_map_iff]
    intro a ha
    have hai : a = j := by
      by_contra hne
      apply ha
      obtain ⟨z, hz⟩ := (Fin.exists_succAbove_eq_iff).mpr hne
      exact ⟨z, hz⟩
    rw [hai]
    exact hj
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq⟩

end MapSupport

end Convexity.StdSimplex
open Topology

section ConvexStdSimplexFaceClosedEmbedding

namespace Convexity.StdSimplex

/-- The new-carrier face inclusion
`Convexity.StdSimplex ℝ (Fin (n + 1)) → Convexity.StdSimplex ℝ (Fin (n + 2))`
that inserts a `0` at coordinate `j` (via `Fin.succAbove j`) is a closed embedding.

Follows from pinned `continuous_map` and the accepted `map_injective`
(`Fin.succAbove_right_injective`), with compactness of the finite source and
Hausdorffness from the weights embedding
(`isEmbedding_toFun_comp_weights`), via
`IsClosedEmbedding.of_continuous_injective_isClosedMap`. -/
theorem isClosedEmbedding_map_succAbove {n : ℕ} (j : Fin (n + 2)) :
    IsClosedEmbedding (map (R := ℝ) (Fin.succAbove j : Fin (n + 1) → Fin (n + 2))) := by
  have hcont : Continuous (map (R := ℝ) (Fin.succAbove j : Fin (n + 1) → Fin (n + 2))) :=
    continuous_map ℝ _
  have hinj : Function.Injective (map (R := ℝ) (Fin.succAbove j : Fin (n + 1) → Fin (n + 2))) :=
    map_injective Fin.succAbove_right_injective
  have : CompactSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) := inferInstance
  have : T2Space (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
    (isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).t2Space
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj hcont.isClosedMap

end Convexity.StdSimplex

end ConvexStdSimplexFaceClosedEmbedding

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KKM

/-!
# Brouwer's fixed-point theorem for the standard simplex

Every continuous self-map of the standard simplex `Δⁿ = Convexity.StdSimplex ℝ (Fin (n + 1))`
has a fixed point. Pinned Mathlib has no Brouwer fixed-point theorem; this module derives the
simplex case from the Knaster–Kuratowski–Mazurkiewicz lemma
(`MathlibExt.Analysis.Convex.KKM.kkm_lemma`), which the repository proves from Sperner's lemma
on iterated barycentric subdivisions. The derivation is the one of the KKM paper, whose title
announces it: for a continuous `f`, the sets `Fᵢ = {x | f(x)ᵢ ≤ xᵢ}` are closed and satisfy the
KKM covering condition, so they have a common point, and at a common point `f(x) = x` because
both weight vectors sum to `1`.

So the chain Sperner ⟹ KKM ⟹ Brouwer, the combinatorial route to Brouwer that underlies the
complexity class PPAD (Papadimitriou 1994; Daskalakis, Goldberg and Papadimitriou 2009,
Section 3.3), is complete in the repository for simplices. The module covers the standard
simplex, simplices on any finite nonempty vertex set (`exists_fixedPoint_of_finite`) and finite
products of such simplices (`exists_fixedPoint_pi`, the form used in Nash's proof); balls and
general compact convex sets are covered by `MathlibExt.Analysis.Convex.BrouwerFixedPoint`.

## Relation to `MathlibExt.Analysis.Convex.BrouwerFixedPoint`

That module proves the simplex case by the same KKM argument (`exists_fixedPoint_stdSimplex`,
the statement of `exists_fixedPoint` here) and extends it to every nonempty compact convex set in
a finite-dimensional real normed space (its `exists_fixedPoint`). It does not state the forms
for other finite vertex sets and products (`exists_fixedPoint_of_finite`, `exists_fixedPoint_pi`).

## References

* B. Knaster, C. Kuratowski, S. Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für
  n-dimensionale Simplexe", Fundamenta Mathematicae 14 (1929), 132–137.
* C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, "The complexity of computing a Nash
  equilibrium", SIAM J. Comput. 39(1) (2009), 195–259, Section 3.3.
-/

@[expose] public section

namespace MathlibExt.Topology.BrouwerFixedPoint

open Convexity

variable {n : ℕ}

/-- **The Brouwer sets satisfy the KKM covering condition.** For every map `f` of the standard
simplex to itself and every point `x`, some coordinate `i` in the support of `x` has
`f(x)ᵢ ≤ xᵢ`: otherwise summing `xᵢ < f(x)ᵢ` over the support would give
`1 < ∑ᵢ f(x)ᵢ = 1`. -/
theorem exists_pos_weights_le (f : StdSimplex ℝ (Fin (n + 1)) → StdSimplex ℝ (Fin (n + 1)))
    (x : StdSimplex ℝ (Fin (n + 1))) :
    ∃ i : Fin (n + 1), 0 < x.weights i ∧ (f x).weights i ≤ x.weights i := by
  classical
  by_contra h
  push Not at h
  set S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => 0 < x.weights i) with hS
  have hSx : ∑ i ∈ S, x.weights i = 1 := by
    rw [hS, Finset.sum_filter_of_ne]
    · exact x.total_of_fintype
    · intro i _ hi
      exact lt_of_le_of_ne (x.weights_nonneg i) (Ne.symm hi)
  have hSne : S.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hSx
    exact zero_ne_one hSx
  have hlt : ∑ i ∈ S, x.weights i < ∑ i ∈ S, (f x).weights i :=
    Finset.sum_lt_sum_of_nonempty hSne (fun i hi => h i (Finset.mem_filter.mp hi).2)
  have hle : ∑ i ∈ S, (f x).weights i ≤ ∑ i, (f x).weights i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => (f x).weights_nonneg i)
  rw [(f x).total_of_fintype, hSx] at *
  linarith

/-- **Brouwer's fixed-point theorem for the standard simplex.** Every continuous map `f` of the
standard simplex `Δⁿ = Convexity.StdSimplex ℝ (Fin (n + 1))` to itself has a fixed point.

Proof: the closed sets `Fᵢ = {x | f(x)ᵢ ≤ xᵢ}` satisfy the KKM condition
(`exists_pos_weights_le`), so by the Knaster–Kuratowski–Mazurkiewicz lemma they share a point
`x`; there `f(x)ᵢ ≤ xᵢ` for every `i` and both sides sum to `1`, so `f(x) = x`. This is the
argument of B. Knaster, C. Kuratowski and S. Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für
n-dimensionale Simplexe", Fundamenta Mathematicae 14 (1929), 132–137. The statement is
Brouwer's theorem restricted to the simplex; it is the form used by Nash-type existence proofs
once strategy spaces are simplices. -/
theorem exists_fixedPoint (f : StdSimplex ℝ (Fin (n + 1)) → StdSimplex ℝ (Fin (n + 1)))
    (hf : Continuous f) : ∃ x, f x = x := by
  classical
  obtain ⟨x, hx⟩ := MathlibExt.Analysis.Convex.KKM.kkm_lemma
    (fun i => {x | (f x).weights i ≤ x.weights i})
    (fun i => isClosed_le ((StdSimplex.continuous_weights_apply ℝ i).comp hf)
      (StdSimplex.continuous_weights_apply ℝ i))
    (fun x => by
      obtain ⟨i, hi, hle⟩ := exists_pos_weights_le f x
      exact ⟨i, hi, hle⟩)
  refine ⟨x, ?_⟩
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), (f x).weights i ≤ x.weights i :=
    fun i _ => hx i
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp
    (by rw [(f x).total_of_fintype, x.total_of_fintype])
  ext i
  exact heq i (Finset.mem_univ i)

/-- **Brouwer's theorem for the simplex, fixed-point form.** A continuous self-map of the
standard simplex has a point `x` with `Function.IsFixedPt f x`; a restatement of
`exists_fixedPoint` in Mathlib's fixed-point vocabulary. -/
theorem exists_isFixedPt (f : StdSimplex ℝ (Fin (n + 1)) → StdSimplex ℝ (Fin (n + 1)))
    (hf : Continuous f) : ∃ x, Function.IsFixedPt f x :=
  exists_fixedPoint f hf

/-! ### Other index types and products of simplices -/

section General

/-- **Probability vector from a function.** A nonnegative function `w` on a finite type with
`∑ₓ w x = 1`, packaged as a point of `Convexity.StdSimplex ℝ X`. -/
noncomputable def ofFun {X : Type*} [Fintype X] (w : X → ℝ) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∑ x, w x = 1) : StdSimplex ℝ X where
  weights := Finsupp.equivFunOnFinite.symm w
  nonneg := fun x => by simpa using h0 x
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simpa using h1

@[simp]
theorem ofFun_weights {X : Type*} [Fintype X] (w : X → ℝ) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∑ x, w x = 1) (x : X) : (ofFun w h0 h1).weights x = w x := by
  simp [ofFun]

/-- **Continuity criterion for maps into a simplex.** A map `g` into `Convexity.StdSimplex ℝ X`
(`X` finite) is continuous as soon as every weight `t ↦ (g t).weights x` is continuous. -/
theorem continuous_of_continuous_weights {T X : Type*} [TopologicalSpace T] [Finite X]
    {g : T → StdSimplex ℝ X} (hg : ∀ x, Continuous fun t => (g t).weights x) : Continuous g := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ X).continuous_iff]
  exact continuous_pi hg

/-- **Brouwer's fixed-point theorem for simplices with any finite vertex set.** Every
continuous self-map of `Convexity.StdSimplex ℝ X`, for a finite nonempty type `X`, has a fixed
point. Transported from `exists_fixedPoint` along an enumeration `X ≃ Fin (n + 1)`. -/
theorem exists_fixedPoint_of_finite {X : Type*} [Finite X] [Nonempty X]
    (f : StdSimplex ℝ X → StdSimplex ℝ X) (hf : Continuous f) : ∃ x, f x = x := by
  have := Fintype.ofFinite X
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card X = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : X ≃ Fin (k + 1) := Fintype.equivFinOfCardEq hk
  obtain ⟨y, hy⟩ := exists_fixedPoint (fun y => (f (y.map e.symm)).map e)
    ((StdSimplex.continuous_map ℝ e).comp (hf.comp (StdSimplex.continuous_map ℝ e.symm)))
  refine ⟨y.map e.symm, ?_⟩
  have h1 : ((f (y.map e.symm)).map e).map e.symm = f (y.map e.symm) := by
    rw [StdSimplex.map_map]
    simp only [Equiv.symm_apply_apply]
    exact StdSimplex.map_id (f (y.map e.symm))
  rw [← h1]
  exact congrArg (fun z => z.map e.symm) hy

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]

/-- **Product distribution.** The product distribution `s ↦ ∏ᵢ σᵢ(sᵢ)` on `∀ i, S i` of
independent distributions `σᵢ` on the finite sets `S i` (in game theory, the distribution of
pure profiles under independent mixed strategies). -/
noncomputable def prodSimplex (σ : ∀ i, StdSimplex ℝ (S i)) : StdSimplex ℝ (∀ i, S i) :=
  ofFun (fun s => ∏ i, (σ i).weights (s i))
    (fun s => Finset.prod_nonneg (fun i _ => (σ i).weights_nonneg (s i)))
    (by rw [← Fintype.prod_sum]; simp)

/-- **Weights of a pushforward distribution.** For a map `g` between finite types, the
pushforward `p.map g` of a distribution `p` gives `y` the total weight `∑_{g x = y} p(x)` of its
preimage; in particular the `i`-th marginal of a distribution on `∀ i, S i` is
`p.map (fun s => s i)`. -/
theorem map_weights_apply {X Y : Type*} [Fintype X] [DecidableEq Y] (g : X → Y)
    (p : StdSimplex ℝ X) (y : Y) :
    (p.map g).weights y = ∑ x ∈ Finset.univ.filter (fun x => g x = y), p.weights x := by
  rw [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (by simp), Finset.sum_filter]
  simp [Finsupp.single_apply]

/-- **The marginals of a product distribution are its factors.** The `i`-th marginal
`(prodSimplex σ).map (fun s => s i)` of the product of independent distributions `σⱼ` is `σᵢ`:
summing `∏ⱼ σⱼ(sⱼ)` over the profiles with `sᵢ = t` leaves `σᵢ(t)`, since every other factor sums
to `1`. -/
theorem marginal_prodSimplex (σ : ∀ i, StdSimplex ℝ (S i)) (i : ι) :
    (prodSimplex σ).map (fun s => s i) = σ i := by
  classical
  ext t
  rw [map_weights_apply]
  simp only [prodSimplex, ofFun_weights]
  rw [Finset.sum_filter]
  set g : ∀ j, S j → ℝ := Function.update (fun j => ⇑(σ j).weights) i
    (fun x => if x = t then (σ i).weights x else 0) with hg
  have hpt : ∀ s : ∀ j, S j,
      (if s i = t then ∏ j, (σ j).weights (s j) else 0) = ∏ j, g j (s j) := by
    intro s
    rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i (fun j => g j (s j))]
    have hrest : ∏ j ∈ ({i} : Finset ι)ᶜ, g j (s j) =
        ∏ j ∈ ({i} : Finset ι)ᶜ, (σ j).weights (s j) :=
      Finset.prod_congr rfl (fun j hj => by
        rw [hg, Function.update_of_ne (by simpa using hj)])
    rw [hrest, hg, Function.update_self]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun s _ => hpt s), ← Fintype.prod_sum,
    Fintype.prod_eq_mul_prod_compl i]
  have hrest : ∏ j ∈ ({i} : Finset ι)ᶜ, ∑ x, g j x = 1 :=
    Finset.prod_eq_one (fun j hj => by
      rw [hg, Function.update_of_ne (by simpa using hj)]
      exact (σ j).total_of_fintype)
  rw [hrest, mul_one, hg, Function.update_self]
  simp

/-- **The product distribution depends continuously on its factors.** Each weight
`∏ᵢ σᵢ(sᵢ)` is a product of coordinate functions, continuous on the product of simplices. -/
theorem continuous_prodSimplex :
    Continuous (prodSimplex : (∀ i, StdSimplex ℝ (S i)) → StdSimplex ℝ (∀ i, S i)) := by
  refine continuous_of_continuous_weights (fun s => ?_)
  simp only [prodSimplex, ofFun_weights]
  exact continuous_finsetProd _ (fun i _ =>
    (StdSimplex.continuous_weights_apply ℝ (s i)).comp (continuous_apply i))

/-- **Brouwer's fixed-point theorem for products of simplices.** Every continuous self-map of
a finite product `∏ᵢ Δ(Sᵢ)` of simplices with nonempty finite vertex sets has a fixed point.
The product is a retract of the simplex `Δ(∏ᵢ Sᵢ)` (product distribution, then marginals), so
the statement follows from `exists_fixedPoint_of_finite`. This is the form of Brouwer's
theorem used in J. Nash, "Non-cooperative games", Ann. of Math. 54 (1951), 286–295, where the
product of the players' mixed-strategy simplices is the domain of the fixed-point map. -/
theorem exists_fixedPoint_pi {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, Finite (S i)]
    [∀ i, Nonempty (S i)]
    (g : (∀ i, StdSimplex ℝ (S i)) → ∀ i, StdSimplex ℝ (S i)) (hg : Continuous g) :
    ∃ σ, g σ = σ := by
  classical
  have := Fintype.ofFinite ι
  have : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  obtain ⟨p, hp⟩ := exists_fixedPoint_of_finite
    (fun p => prodSimplex (g (fun i => p.map (fun s => s i))))
    (continuous_prodSimplex.comp
      (hg.comp (continuous_pi fun i => StdSimplex.continuous_map ℝ (fun s : ∀ i, S i => s i))))
  refine ⟨fun i => p.map (fun s => s i), ?_⟩
  funext i
  have := congrArg (fun q => q.map (fun s => s i)) hp
  simp only [marginal_prodSimplex] at this
  exact this

end General

end MathlibExt.Topology.BrouwerFixedPoint

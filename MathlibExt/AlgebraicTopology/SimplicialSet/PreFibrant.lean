/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexQuasicategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.Join
public import MathlibExt.AlgebraicTopology.SimplicialSet.FullSubcomplex

/-!
# Pre-fibrant simplicial sets

Stevenson, Definition 3.1, verbatim:

> Definition 3.1. We will say that simplicial set S is pre-fibrant if
> it satisfies the following conditions:
> (i) every map Λ²₁ → S extends along the inclusion Λ²₁ ⊆ Δ².
> (ii) for every 0 < i < n, if f : Λⁿᵢ → S is a map such that d₀f is a
> constant (n−1)-simplex, then f extends along the inclusion
> Λⁿᵢ ⊆ Δⁿ.
> Here we will say that an n-simplex x ∈ S is constant if
> x = s₀ⁿ(v) for some vertex v of S.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

variable {S T X : SSet.{u}}

/-!
### Constant simplices
-/

/-- The constant `n`-simplex of `S` at a vertex `v`: the image of
`v` under the (unique) map induced by `⦋n⦌ ⟶ ⦋0⦌`. By
`constSimplex_zero` and `constSimplex_succ` this is Stevenson's
`s₀ⁿ(v)`, the `n`-fold iterate of the `0`-th degeneracy. -/
def constSimplex (S : SSet.{u}) (n : ℕ) (v : S _⦋0⦌) : S _⦋n⦌ :=
  S.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op v

/-- The constant `0`-simplex at `v` is `v`. -/
@[simp]
lemma constSimplex_zero (v : S _⦋0⦌) : constSimplex S 0 v = v := by
  simp [constSimplex]

/-- The constant `(n+1)`-simplex at `v` is the `0`-th degeneracy of
the constant `n`-simplex at `v`; inductively,
`constSimplex S n v = s₀ⁿ(v)` in Stevenson's notation. -/
lemma constSimplex_succ (n : ℕ) (v : S _⦋0⦌) :
    constSimplex S (n + 1) v = S.σ (0 : Fin (n + 1)) (constSimplex S n v) := by
  have h : (SimplexCategory.const ⦋n + 1⦌ ⦋0⦌ 0) =
      SimplexCategory.σ (0 : Fin (n + 1)) ≫ SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 :=
    Subsingleton.elim _ _
  calc constSimplex S (n + 1) v
      = S.map (SimplexCategory.σ (0 : Fin (n + 1)) ≫
          SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op v := by rw [constSimplex, h]
    _ = S.σ (0 : Fin (n + 1)) (constSimplex S n v) := by
        simp [constSimplex, SimplicialObject.σ_def]

/-- The simplex classified by the constant map `Δ[n] ⟶ S` at a vertex
`v` is the constant `n`-simplex at `v`. -/
lemma yonedaEquiv_const_eq (n : ℕ) (v : S _⦋0⦌) :
    yonedaEquiv (SSet.const v : Δ[n] ⟶ S) = constSimplex S n v := by
  have h1 : (SSet.const v : Δ[n] ⟶ S) =
      stdSimplex.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0) ≫
        (SSet.const v : Δ[0] ⟶ S) := by
    rw [SSet.comp_const]
  rw [h1, ← yonedaEquiv_naturality, yonedaEquiv_const]
  rfl

/-- A simplex is *constant* if it is `s₀ⁿ(v)` for some vertex `v`
(Stevenson's terminology before Definition 3.1). -/
def IsConstantSimplex {n : ℕ} (x : S _⦋n⦌) : Prop :=
  ∃ v : S _⦋0⦌, x = constSimplex S n v

/-- Constant simplices are constant. -/
lemma isConstantSimplex_constSimplex (n : ℕ) (v : S _⦋0⦌) :
    IsConstantSimplex (constSimplex S n v) :=
  ⟨v, rfl⟩

/-- Constant simplices are preserved by simplicial maps. -/
lemma IsConstantSimplex.map {n : ℕ} {x : S _⦋n⦌} (hx : IsConstantSimplex x)
    (p : S ⟶ T) : IsConstantSimplex (p.app _ x) := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨p.app _ v, ?_⟩
  exact NatTrans.naturality_apply p _ v

/-- A map out of a standard simplex classifies a constant simplex if
and only if it is a constant map at some vertex. -/
lemma isConstantSimplex_yonedaEquiv_iff {n : ℕ} (f : Δ[n] ⟶ S) :
    IsConstantSimplex (yonedaEquiv f) ↔ ∃ v : S _⦋0⦌, f = SSet.const v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, yonedaEquiv.injective ?_⟩
    rw [hv, yonedaEquiv_const_eq]
  · rintro ⟨v, rfl⟩
    rw [yonedaEquiv_const_eq]
    exact isConstantSimplex_constSimplex n v

/-!
### The `0`-th face of a horn map
-/

/-- The `0`-th face of a horn map `f : Λ[n+2, i] ⟶ S`, as an
`(n+1)`-simplex of `S`: Stevenson's `d₀f`. It is the image under
`f` of the `0`-th codimension-one face of the horn, which exists
because `i ≠ 0`. -/
def hornFaceZero {n : ℕ} {i : Fin (n + 3)} (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S)
    (h : (0 : Fin (n + 3)) ≠ i) : S _⦋n + 1⦌ :=
  f.app _ (horn.face i 0 h)

/-- The `0`-th face of a composite horn map is the image of the
`0`-th face. -/
@[simp]
lemma hornFaceZero_comp {n : ℕ} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h : (0 : Fin (n + 3)) ≠ i)
    (p : S ⟶ T) : hornFaceZero (f ≫ p) h = p.app _ (hornFaceZero f h) :=
  rfl

/-- The `0`-th face of a horn map is the simplex classified by
restricting the horn map along the face inclusion
`Δ[n+1] ⟶ Λ[n+2, i]` opposite vertex `0`; this is `d₀f` as a map,
the form used in Stevenson's pullback arguments. -/
lemma hornFaceZero_eq_yonedaEquiv {n : ℕ} {i : Fin (n + 3)}
    (f : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h : (0 : Fin (n + 3)) ≠ i) :
    hornFaceZero f h = yonedaEquiv (horn.ι i 0 h ≫ f) := by
  rw [hornFaceZero, yonedaEquiv_comp, horn.yonedaEquiv_ι]

/-!
### Pre-fibrant simplicial sets
-/

/-- A simplicial set `S` is *pre-fibrant* (Stevenson, Definition 3.1)
if every `Λ[2, 1]`-horn in `S` fills, and every inner horn in `S`
whose `0`-th face is a constant simplex fills. -/
class IsPreFibrant (S : SSet.{u}) : Prop where
  hornFillingTwo' : ∀ (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ S),
    ∃ σ : Δ[2] ⟶ S, σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ
  hornFillingConst' : ∀ ⦃n : ℕ⦄ ⦃i : Fin (n + 3)⦄
    (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (_h0 : 0 < i)
    (_hn : i < Fin.last (n + 2)),
    IsConstantSimplex (hornFaceZero σ₀ (ne_of_lt _h0)) →
      ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ

namespace IsPreFibrant

variable [IsPreFibrant S]

/-- In a pre-fibrant simplicial set, every `Λ[2, 1]`-horn fills
(Definition 3.1(i)). -/
lemma hornFillingTwo (σ₀ : (Λ[2, (1 : Fin 3)] : SSet.{u}) ⟶ S) :
    ∃ σ : Δ[2] ⟶ S, σ₀ = Λ[2, (1 : Fin 3)].ι ≫ σ :=
  hornFillingTwo' σ₀

/-- In a pre-fibrant simplicial set, every inner horn whose `0`-th
face is constant fills (Definition 3.1(ii)). -/
lemma hornFillingConst {n : ℕ} {i : Fin (n + 3)}
    (σ₀ : (Λ[n + 2, i] : SSet.{u}) ⟶ S) (h0 : 0 < i)
    (hn : i < Fin.last (n + 2))
    (hconst : IsConstantSimplex (hornFaceZero σ₀ (ne_of_lt h0))) :
    ∃ σ : Δ[n + 2] ⟶ S, σ₀ = Λ[n + 2, i].ι ≫ σ :=
  hornFillingConst' σ₀ h0 hn hconst

end IsPreFibrant

/-- Every quasicategory (Stevenson's `∞`-category) is pre-fibrant
(Stevenson, Example 3.2): both filling conditions are special cases
of inner horn filling. -/
instance (S : SSet.{u}) [Quasicategory S] : IsPreFibrant S where
  hornFillingTwo' σ₀ := Quasicategory.hornFilling (by decide) (by decide) σ₀
  hornFillingConst' n i σ₀ h0 hn _ := Quasicategory.hornFilling' σ₀ h0 hn

/-- Being pre-fibrant is invariant under isomorphism of simplicial
sets. -/
lemma isPreFibrant_of_iso {A B : SSet.{u}} (e : A ≅ B) [IsPreFibrant B] :
    IsPreFibrant A where
  hornFillingTwo' σ₀ := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingTwo (S := B) (σ₀ ≫ e.hom)
    exact ⟨σ ≫ e.inv, by
      rw [← Category.assoc, ← hσ, Category.assoc, e.hom_inv_id,
        Category.comp_id]⟩
  hornFillingConst' n i σ₀ h0 hn hconst := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingConst (S := B) (σ₀ ≫ e.hom)
      h0 hn (by rw [hornFaceZero_comp]; exact hconst.map e.hom)
    exact ⟨σ ≫ e.inv, by
      rw [← Category.assoc, ← hσ, Category.assoc, e.hom_inv_id,
        Category.comp_id]⟩

/-- If `p : X → S` is an inner fibration and `S` is pre-fibrant,
then `X` is pre-fibrant (Stevenson, Remark 3.4, first part): fill
the horn in `S` and lift the filler along `p`; constancy of the
`0`-th face is preserved by `p`. -/
lemma isPreFibrant_of_innerFibration (p : X ⟶ S) [InnerFibration p]
    [IsPreFibrant S] : IsPreFibrant X where
  hornFillingTwo' σ₀ := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingTwo (S := S) (σ₀ ≫ p)
    have : HasLiftingProperty Λ[2, (1 : Fin 3)].ι p :=
      InnerFibration.mem _
        (horn_ι_mem_innerHornInclusions (by decide) (by decide))
    let sq : CommSq σ₀ Λ[2, (1 : Fin 3)].ι p σ := CommSq.mk hσ
    exact ⟨sq.lift, sq.fac_left.symm⟩
  hornFillingConst' n i σ₀ h0 hn hconst := by
    obtain ⟨σ, hσ⟩ := IsPreFibrant.hornFillingConst (S := S) (σ₀ ≫ p)
      h0 hn (by rw [hornFaceZero_comp]; exact hconst.map p)
    have : HasLiftingProperty Λ[n + 2, i].ι p :=
      InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)
    let sq : CommSq σ₀ Λ[n + 2, i].ι p σ := CommSq.mk hσ
    exact ⟨sq.lift, sq.fac_left.symm⟩

/-- A full subcomplex of a pre-fibrant simplicial set is pre-fibrant
(Stevenson, Remark 3.4, second part), since the inclusion of a full
subcomplex is an inner fibration. -/
instance (S : Set (X _⦋0⦌)) [IsPreFibrant X] :
    IsPreFibrant (Subcomplex.full S : SSet.{u}) :=
  isPreFibrant_of_innerFibration (Subcomplex.full S).ι

/-- The join of two standard simplices is pre-fibrant, since
`Δ[m] ⋆ Δ[n] ≅ Δ[m + n + 1]` is a quasicategory. -/
instance (m n : ℕ) : IsPreFibrant ((Δ[m] : SSet.{u}) ⋆ Δ[n]) :=
  isPreFibrant_of_iso (joinStdSimplexIso m n)

/-!
### Inner-anodyne replacement by a pre-fibrant simplicial set
-/

/-- The functorial factorization of `X → ⊤` produced by the inner
horn small object argument: an inner anodyne map (in
`innerHornInclusions.rlp.llp = innerAnodyneExtensions`) followed by
an inner fibration (in `innerHornInclusions.rlp =
innerFibrations`). -/
noncomputable def preFibrantReplacementData (X : SSet.{u}) :
    MorphismProperty.MapFactorizationData innerHornInclusions.rlp.llp
      innerHornInclusions.rlp (terminal.from X) :=
  MorphismProperty.factorizationData _ _ _

/-- The replacement target of `X`: the middle object of
`preFibrantReplacementData X`. It is a quasicategory (hence
pre-fibrant), reached from `X` by an inner anodyne map. This is the
full small-object replacement, not Stevenson's selective
constructions in Propositions 3.5 and 4.12; see the file header. -/
noncomputable abbrev preFibrantReplacement (X : SSet.{u}) : SSet.{u} :=
  (preFibrantReplacementData X).Z

/-- The replacement map from a simplicial set to its (quasicategory,
hence pre-fibrant) replacement. -/
noncomputable def toPreFibrantReplacement (X : SSet.{u}) :
    X ⟶ preFibrantReplacement X :=
  (preFibrantReplacementData X).i

/-- The replacement map is inner anodyne. -/
lemma innerAnodyneExtensions_toPreFibrantReplacement (X : SSet.{u}) :
    innerAnodyneExtensions (toPreFibrantReplacement X) := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  exact (preFibrantReplacementData X).hi

/-- The map from the replacement to the terminal object is an inner
fibration. -/
instance : InnerFibration (preFibrantReplacementData X).p :=
  ⟨(preFibrantReplacementData X).hp⟩

/-- The replacement of any simplicial set is a quasicategory. -/
instance (X : SSet.{u}) : Quasicategory (preFibrantReplacement X) :=
  (quasicategory_iff_of_isTerminal _ terminalIsTerminal).mpr
    ⟨(preFibrantReplacementData X).hp⟩

/-- Every simplicial set admits an inner anodyne map to a
pre-fibrant simplicial set. The target here is in fact a
quasicategory, by the full inner horn small object argument;
Stevenson's Proposition 4.12 constructs a smaller merely
pre-fibrant target with a descent property, which this map does not
have (see the file header). -/
theorem exists_innerAnodyneExtensions_and_isPreFibrant (X : SSet.{u}) :
    ∃ (T : SSet.{u}) (f : X ⟶ T), innerAnodyneExtensions f ∧ IsPreFibrant T :=
  ⟨preFibrantReplacement X, toPreFibrantReplacement X,
    innerAnodyneExtensions_toPreFibrantReplacement X, inferInstance⟩

/-- Every simplicial set admits an inner anodyne map to a
quasicategory (the replacement actually constructed here). -/
theorem exists_innerAnodyneExtensions_and_quasicategory (X : SSet.{u}) :
    ∃ (T : SSet.{u}) (f : X ⟶ T), innerAnodyneExtensions f ∧ Quasicategory T :=
  ⟨preFibrantReplacement X, toPreFibrantReplacement X,
    innerAnodyneExtensions_toPreFibrantReplacement X, inferInstance⟩

end SSet

end

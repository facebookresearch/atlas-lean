/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChangeGeneral
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexHornAttachment
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! # Prism triangulation and cobase change along monos (packet T43)

This module is the prism-triangulation attack on TODO(T34-A) of
`CobaseChangeGeneral.lean` (the prism strict extension property
`SSet.HoPrePrismStrictExtension i C` for every monomorphism
`i : A ⟶ B` and quasicategory `C`). The sections below give the
full informal proof; what is formalized here is the complete
combinatorial core for the source-prescribed `Δ[1]`-prism over a
cell: the values of the top simplices `τₖ` and the ranges of the
diagonal simplices (the ranges of the `τₖ` themselves are
`SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff`
and `SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff`
in `ProdStdSimplexOneCompat.lean`), the face analysis, the general
pushout that attaches one simplex along a horn (in the neutral module
`SubcomplexHornAttachment.lean`:
`SSet.Subcomplex.isPushout_hornAttach`,
`SSet.Subcomplex.exists_extension_sup_of_horn_filler`; the
classifying maps of the `τₖ` are the inclusions
`SSet.prodStdSimplex₁.ι`, whose monomorphicity — hence injectivity
on simplices — is the instance from `ProdStdSimplexOneCompat.lean`),
the decreasing filtration
`SSet.prismSrcFilt` with its steps, top, and bottom, and the
attaching-horn computation
(`SSet.prismSrcFilt_preimage_prismTauMap`: the preimage of
`Gₖ₊₁` under `τₖ` is `Λ[n+1, k]`), together with the vertical
edge `SSet.prismVertZero` and its membership in the initial
subcomplex. What remains to close TODO(T34-A) is exactly:
(i) identify `τ₀` over the `(0,1)`-edge of `Δ[n+1]` with
`SSet.prismVertZero` (so the last horn is special by
`SSet.Edge.IsEquivalence.eval_vertex`) and run the finite
induction attaching the `τₖ` with
`SSet.Subcomplex.exists_extension_sup_of_horn_filler`, the
`n = 0` cell by a
degenerate prism; (ii) the mirror (target-prescribed) filtration;
(iii) the `Δ[2]`-prism shuffle filtration of §2 and the pointwise
criterion; (iv) the skeletal closures of §3 and the assembly of
§4 feeding `SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`
(packet T30). TODO(T34-B2) (faithfulness) is untouched, and no
statement here claims cobase-change stability of
`SSet.categoricalEquivalences` along monomorphisms.

## 0. What has to be proved

Fix `i : A ⟶ B`, `[Mono i]`, `C` a quasicategory, a vertex `b` of
`Fun(B, C) := (ihom B).obj C` and an equivalence edge
`e : Edge ((pre i)^* b) a'` of `Fun(A, C)`. Through the prism
dictionary of `IhomPrism.lean`, `e` is a prism
`H : A ⊗ Δ[1] ⟶ C` whose source end `A ⊗ {0}` is `i ≫ b♯`, where
`b♯ : B ⟶ C` classifies `b`. A strict lift is a prism
`F : B ⊗ Δ[1] ⟶ C` with `(i ▷ Δ[1]) ≫ F = H`, source end `b♯`, and
whose associated edge of `Fun(B, C)` is an equivalence. The proof
has three layers: prism extension along boundary inclusions by
triangulation (§1, §2), formal closure of the extension properties
under the relative skeletal filtration (§3), and the pointwise
criterion that the lifted edge is an equivalence (§2, §4).

## 1. The `Δ[1]`-prism over a cell

Let `i = ∂Δ[n].ι`, `n ≥ 1`. The data `(H, b♯)` is a map out of the
subcomplex `S₀ := ∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` of `Δ[n] ⊗ Δ[1]`
(formally `Subcomplex.unionProd ∂Δ[n] (stdSimplex.face {0})`, glued
by `Subcomplex.unionProd.isPushout`). Vertices of the prism are
pairs `(i, ε)`. Its nondegenerate `(n+1)`-simplices are, upstream
(`SSet.prodStdSimplex₁.nonDegenerateEquiv`),
`τₖ = ((0,0), …, (k,0), (k,1), …, (n,1))`, `k : Fin (n+1)`. Attach
them in decreasing order `k = n, …, 0` to
`Gₖ₊₁ := S₀ ∪ τₙ ∪ … ∪ τₖ₊₁`. The faces of `τₖ`: `dₖ₊₁` (omitting
`(k,1)`) is the diagonal `n`-simplex shared with `τₖ₊₁`
(upstream `codimOneSimplex`), and for `k = n` it is the bottom
`Δ[n] ⊗ {0}`; `dⱼ` for `j ∉ {k, k+1}` misses a first coordinate,
hence lies in `∂Δ[n] ⊗ Δ[1]`; the only new face is `dₖ` (omitting
`(k,0)`). So `τₖ` is attached along `Λ[n+1, k]` (formally: the
preimage of `Gₖ₊₁` under `yonedaEquiv.symm τₖ` is that horn, and
the attaching square is a pushout because `τₖ`, being an injective
chain in the poset `Fin (n+1) × Fin 2`, induces an injective map on
simplices). For `1 ≤ k ≤ n` the horn is inner and is filled in `C`
by `Quasicategory.hornFilling`. For `k = 0` it is `Λ[n+1, 0]`,
whose `(0,1)`-edge (`SSet.leftHornEdge`) is the vertical edge
`(0,0) ⟶ (0,1)`, i.e. the evaluation of `e` at vertex `0` — an
equivalence by `SSet.Edge.IsEquivalence.eval_vertex` (packet T34) —
and is filled by `SSet.exists_fill_horn_left_of_isEquivalence`
(packet T21). The mirror filtration (increasing order, attaching
along `Λ[n+1, k+1]`, last step the right horn `Λ[n+1, n+1]` filled
by `SSet.exists_fill_horn_right_of_isEquivalence`) gives the
target-prescribed variant from initial data on
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {1}`. For `n = 0` both are the degenerate
edge at the prescribed vertex (`Λ[1, 0]`/`Λ[1, 1]` filled by a
degeneracy). This proves the `Δ[1]`-prism extension properties
`SSet.exists_extension_of_unionProd_boundary_face_zero/one` in
subcomplex form: maps out of the unionProd extend to the prism as
soon as the single relevant vertical edge is an equivalence.

## 2. The `Δ[2]`-prism and the pointwise criterion

The prism `F` of §1 is an edge `ε` of `Fun(B, C)` restricting
strictly to `e`, all of whose vertex evaluations are equivalences
(the verticals over `∂Δ[n]` are prescribed, and every vertex of
`Δ[n]` lies in `∂Δ[n]` for `n ≥ 1`). To see `ε` is an equivalence
(`IsIso (HomotopyCategory.homMk ε)`) we produce two one-sided inverses. Let
`e⁻¹` be inverse data for `e`
(`SSet.Edge.IsEquivalence.nonempty_invStruct`): `CompStruct`
witnesses `α : e ≫ e⁻¹ = id`, `β : e⁻¹ ≫ e = id` in `Fun(A, C)`,
i.e. prisms `A ⊗ Δ[2] ⟶ C`. A `CompStruct` for `ε` against an
unknown inverse edge `φ` with composite `id` is a prism
`B ⊗ Δ[2] ⟶ C` prescribed on `A ⊗ Δ[2]` (by `α`) and on
`B ⊗ Λ₂` where `Λ₂ ⊆ Δ[2]` is the union of the two faces
corresponding to `ε` (prescribed by `F`) and to the composite
(prescribed by the degenerate prism at the source vertex); the
third face is the output `φ`, whose endpoints are forced.
Cell by cell this is extension from
`∂Δ[n] ⊗ Δ[2] ∪ Δ[n] ⊗ Λ[2, 0]` (resp. `Λ[2, 2]`) to
`Δ[n] ⊗ Δ[2]`. The top simplices are the shuffles
`τ_{a,b} = ((0,0), …, (a,0), (a,1), …, (b,1), (b,2), …, (n,2))`,
`0 ≤ a ≤ b ≤ n`. Attached in lexicographically decreasing `(b, a)`
order (resp. increasing for the mirror), each `τ_{a,b}` has all
faces in the initial subcomplex or in earlier shuffles except one
diagonal face: faces missing a first coordinate lie in
`∂Δ[n] ⊗ Δ[2]`, faces missing a second coordinate `≠ 0` (resp.
`≠ 2`) lie in `Δ[n] ⊗ Λ[2, 0]` (resp. `Λ[2, 2]`), of the diagonal
faces all but one are shared with an earlier shuffle or lie over a
prescribed face of `Δ[2]`, and the extremal attachments are
special outer horns whose special edge is a vertical edge of the
prescribed face prism `F` or of the degenerate prism — pointwise
equivalences. This gives the `Δ[2]`-prism horn extension
properties for boundary inclusions. The two fillers (for `α` and
for `β`) give edges `φ, φ'` of `Fun(B, C)` with
`(HomotopyCategory.homMk ε) ≫ (HomotopyCategory.homMk φ) = 𝟙` and `(HomotopyCategory.homMk φ') ≫
(HomotopyCategory.homMk ε) = 𝟙`
(`HomotopyCategory.homMk_comp_homMk`), so `(HomotopyCategory.homMk ε)` is an isomorphism with
inverse `(HomotopyCategory.homMk φ)`: `ε` is an equivalence. In particular: **an
edge of `Fun(B, C)` which restricts strictly to an equivalence
edge of `Fun(A, C)` and whose vertex evaluations are equivalences
is an equivalence** (the pointwise criterion,
`SSet.Edge.IsEquivalence.of_strict_restriction_pointwise`).

## 3. Skeletal closure

The extension properties of §1 and §2 are properties `Q(i)` of a
map `i` with no equivalence conclusion — only existence of prism
extensions — so they are stable under the formal gluing
operations: under pushout because `(pushout) ⊗ Δ[m]` is the
pushout of the prisms (`Functor.map_isPushout (tensorRight _)`),
under coproducts componentwise, and under sequential composition
by dependent choice along the tower of partial prisms (the colimit
is computed by `tensorRight`, a left adjoint). Upstream
(`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`), a
monomorphism `i` has the relative skeletal filtration
`skeletonOfMono i : ℕ →o B.Subcomplex` with
`skeletonOfMono i 0 = range i`, `⨆ = ⊤`, and each step a pushout
of a coproduct of boundary inclusions
(`relativeCellComplexOfMono.isPushout`). Hence `Q(∂Δ[n].ι)` for
all `n` implies `Q(i)` for every monomorphism `i`, and §2 applies
along `i` itself. No separate closure of
`HoPrePrismStrictExtension` under pushout is needed: the property
is assembled at the end from prism extension along `i` (§1, §3)
plus the pointwise criterion along `i` (§2, §3).

## 4. Assembly

Given `e, b` as in §0: §1+§3 produce the prism `F` extending `H`
with source `b`; every vertex vertical of `F` is an equivalence
(on `A` by `eval_vertex`, at new `0`-cells the chosen prism is
degenerate); §2+§3 (the pointwise criterion) show its edge is an
equivalence. This is `SSet.HoPrePrismStrictExtension i C`
(`SSet.hoPrePrismStrictExtension_of_mono`, with the boundary case
`SSet.hoPrePrismStrictExtension_boundary` recorded separately).
Packet T30/T34 assemblies then give
`SSet.hoFunctor_pre_isIsofibration_of_mono` (TODO(T26-A) in
general — now proved unconditionally in `DwyerKanFinal.lean`),
`SSet.innerIsoFibrations_pre_app_of_mono`, and
essential surjectivity plus fullness for cobase changes. The
unconditional instance
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet)` still requires
TODO(T34-B2) (faithfulness); no statement here claims it.

## References

* J. Lurie, *Higher Topos Theory*, §2.3 (Proposition 2.3.4.5).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2.
* *Kerodon*, §4.5, Corollary 4.5.4.14.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

/-! ## Combinatorics of the prism `Δ[n] ⊗ Δ[1]`

The nondegenerate top simplices `τₖ` are upstream
(`SSet.prodStdSimplex₁.nonDegenerateEquiv`); through
`SSet.prodStdSimplex.objEquiv` they are the chains
`(0,0), …, (k,0), (k,1), …, (n,1)` in `Fin (n+1) × Fin 2`. We
record their values, the values and ranges of the
diagonal simplices `SSet.prodStdSimplex₁.codimOneSimplex`, and the
face analysis of §1 of the header: omitting any vertex of `τₖ`
other than `(k,0)` or `(k,1)` deletes a first coordinate. The
ranges of the `τₖ` are not re-derived here: they are
`SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff`
and `SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff`
from `ProdStdSimplexOneCompat.lean`. -/

section PrismCombinatorics

variable {n : ℕ}

/-- The `k`-th nondegenerate `(n+1)`-simplex of the prism
`Δ[n] ⊗ Δ[1]`: the chain `(0,0), …, (k,0), (k,1), …, (n,1)`
(upstream `SSet.prodStdSimplex₁.nonDegenerateEquiv`). The explicit
`n` is kept because the filtration and attaching statements below
(and their downstream uses) index simplices by `(n, k)` in
simplex positions; the abbreviation is definitionally the
underlying simplex of `nonDegenerateEquiv k`, as recorded in
`SSet.prismTau_eq_nonDegenerateEquiv_val`. -/
noncomputable abbrev prismTau (n : ℕ) (k : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋n + 1⦌ :=
  (prodStdSimplex₁.nonDegenerateEquiv k).1

/-- Bridge to the upstream enumeration: `prismTau n k` is the
underlying simplex of `SSet.prodStdSimplex₁.nonDegenerateEquiv k`.
Hence the `nonDegenerateEquiv` API applies to `prismTau`
directly: values by
`SSet.prodStdSimplex₁.nonDegenerateEquiv_fst` and
`SSet.prodStdSimplex₁.nonDegenerateEquiv_snd`, faces by
`SSet.prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv` and
`SSet.prodStdSimplex₁.δ_succ_nonDegenerateEquiv`, and ranges by
`SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₀_iff`
and `SSet.prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff`. -/
lemma prismTau_eq_nonDegenerateEquiv_val (k : Fin (n + 1)) :
    prismTau n k =
      (prodStdSimplex₁.nonDegenerateEquiv k).val :=
  rfl

/-- The map `Δ[n+1] ⟶ Δ[n] ⊗ Δ[1]` classifying `prismTau n k`:
this is the inclusion `SSet.prodStdSimplex₁.ι k` of
`ProdStdSimplexOneCompat.lean` (with its `Mono` instance and the
`ι_fst`/`ι_snd`/`yonedaEquiv_ι` API), renamed only to keep the
explicit `(n, k)` indexing of the filtration statements below. -/
noncomputable abbrev prismTauMap (n : ℕ) (k : Fin (n + 1)) :
    Δ[n + 1] ⟶ (Δ[n] ⊗ Δ[1] : SSet.{u}) :=
  prodStdSimplex₁.ι k

set_option backward.isDefEq.respectTransparency.types false in
/-- First coordinates of `τₖ`: at position `t` the value is `t`
for `t ≤ k` and `t - 1` afterwards (`σ k` is `Fin.predAbove k`). -/
lemma prismTau_objEquiv_fst_val (k : Fin (n + 1)) (t : Fin (n + 2)) :
    ((prodStdSimplex.objEquiv (prismTau n k) t).1).val =
      if t.val ≤ k.val then t.val else t.val - 1 := by
  have hf : (prismTau n k).1 =
      stdSimplex.objEquiv.symm (SimplexCategory.σ k) :=
    prodStdSimplex₁.nonDegenerateEquiv_fst k
  rw [prodStdSimplex.objEquiv_apply_fst, hf,
    stdSimplex.objEquiv_symm_apply]
  have hσ : (SimplexCategory.σ k).toOrderHom t = k.predAbove t := rfl
  rw [hσ]
  by_cases h : t.val ≤ k.val
  · have hle : t ≤ k.castSucc := h
    rw [Fin.predAbove_of_le_castSucc _ _ hle]
    simp only [h, ↓reduceIte]
    rfl
  · have hlt : k.castSucc < t := by
      rw [Fin.lt_def, Fin.val_castSucc]
      omega
    rw [Fin.predAbove_of_castSucc_lt _ _ hlt, Fin.val_pred]
    simp only [h, ↓reduceIte]

set_option backward.isDefEq.respectTransparency.types false in
/-- Second coordinates of `τₖ`: `0` up to position `k`, then `1`. -/
lemma prismTau_objEquiv_snd (k : Fin (n + 1)) (t : Fin (n + 2)) :
    (prodStdSimplex.objEquiv (prismTau n k) t).2 =
      if t.val ≤ k.val then 0 else 1 := by
  have hs : (prismTau n k).2 =
      stdSimplex.objMk₁ k.succ.castSucc :=
    prodStdSimplex₁.nonDegenerateEquiv_snd k
  rw [prodStdSimplex.objEquiv_apply_snd, hs,
    stdSimplex.objMk₁_apply]
  have hv : (k.succ.castSucc).val = k.val + 1 := by simp
  have hcond : (t.castSucc < k.succ.castSucc) ↔ t.val ≤ k.val := by
    rw [Fin.lt_def, Fin.val_castSucc, hv]
    omega
  by_cases h : t.val ≤ k.val
  · simp only [h, hcond.2 h, ↓reduceIte]
  · simp only [h, mt hcond.1 h, ↓reduceIte]

/-- The first coordinate of `τₖ` takes the value `i` exactly at
position `i` (when `i ≤ k`) and at position `i + 1` (when
`k ≤ i`); both occur for `i = k`. -/
lemma prismTau_objEquiv_fst_val_eq_iff {k : Fin (n + 1)}
    {t : Fin (n + 2)} {i : Fin (n + 1)} :
    ((prodStdSimplex.objEquiv (prismTau n k) t).1).val = i.val ↔
      (t.val = i.val ∧ i.val ≤ k.val) ∨
        (t.val = i.val + 1 ∧ k.val ≤ i.val) := by
  rw [prismTau_objEquiv_fst_val]
  by_cases h : t.val ≤ k.val
  · simp only [h, ↓reduceIte]
    constructor
    · intro h2
      exact Or.inl ⟨h2, h2 ▸ h⟩
    · rintro (⟨h2, _⟩ | ⟨h2, h3⟩)
      · exact h2
      · omega
  · simp only [h, ↓reduceIte]
    constructor
    · intro h2
      refine Or.inr ⟨by omega, by omega⟩
    · rintro (⟨h2, h3⟩ | ⟨h2, _⟩)
      · omega
      · omega

lemma codimOne_fst (j : Fin (n + 2)) :
    ((prodStdSimplex₁.codimOneSimplex j).1).1 =
      stdSimplex.objMk .id :=
  rfl

lemma codimOne_snd (j : Fin (n + 2)) :
    ((prodStdSimplex₁.codimOneSimplex j).1).2 =
      stdSimplex.objMk₁ j :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- First coordinates of the diagonal simplex
`codimOneSimplex j` are the identity. -/
lemma codimOne_objEquiv_fst (j : Fin (n + 2)) (t : Fin (n + 1)) :
    (prodStdSimplex.objEquiv (prodStdSimplex₁.codimOneSimplex j).1 t).1 =
      t := by
  rw [prodStdSimplex.objEquiv_apply_fst, codimOne_fst,
    stdSimplex.objMk_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Second coordinates of the diagonal simplex
`codimOneSimplex j`: `0` before position `j`, then `1`. -/
lemma codimOne_objEquiv_snd (j : Fin (n + 2)) (t : Fin (n + 1)) :
    (prodStdSimplex.objEquiv (prodStdSimplex₁.codimOneSimplex j).1 t).2 =
      if t.val < j.val then 0 else 1 := by
  rw [prodStdSimplex.objEquiv_apply_snd, codimOne_snd,
    stdSimplex.objMk₁_apply]
  have hcond : (t.castSucc < j) ↔ t.val < j.val := by
    rw [Fin.lt_def, Fin.val_castSucc]
  by_cases h : t.val < j.val
  · simp only [h, hcond.2 h, ↓reduceIte]
  · simp only [h, mt hcond.1 h, ↓reduceIte]

set_option backward.isDefEq.respectTransparency.types false in
/-- The range of the diagonal simplex `codimOneSimplex j` is
`{(i,0) | i < j} ∪ {(i,1) | j ≤ i}`. -/
lemma mem_range_codimOne_objEquiv {j : Fin (n + 2)}
    {p : Fin (n + 1) × Fin 2} :
    p ∈ Set.range
        (prodStdSimplex.objEquiv (prodStdSimplex₁.codimOneSimplex j).1) ↔
      (p.2.val = 0 ∧ p.1.val < j.val) ∨
        (p.2.val = 1 ∧ j.val ≤ p.1.val) := by
  constructor
  · rintro ⟨t, ht⟩
    have ht1 : t = p.1 := by
      have := congrArg Prod.fst ht
      rwa [codimOne_objEquiv_fst] at this
    subst ht1
    by_cases h : p.1.val < j.val
    · refine Or.inl ⟨?_, h⟩
      rw [← ht]
      rw [codimOne_objEquiv_snd]
      simp only [h, ↓reduceIte]
      rfl
    · refine Or.inr ⟨?_, by omega⟩
      rw [← ht]
      rw [codimOne_objEquiv_snd]
      simp only [h, ↓reduceIte]
      rfl
  · rintro (⟨h2, h1⟩ | ⟨h2, h1⟩)
    · refine ⟨p.1, Prod.ext ?_ ?_⟩
      · rw [codimOne_objEquiv_fst]
      · apply Fin.ext
        rw [codimOne_objEquiv_snd]
        simp only [h1, ↓reduceIte]
        exact h2.symm
    · refine ⟨p.1, Prod.ext ?_ ?_⟩
      · rw [codimOne_objEquiv_fst]
      · apply Fin.ext
        rw [codimOne_objEquiv_snd]
        simp only [show ¬ p.1.val < j.val from by omega, ↓reduceIte]
        exact h2.symm

/-- Faces in the prism read through `objEquiv` are
precomposition with `Fin.succAbove`. This is
`SSet.prodStdSimplex.objEquiv_δ_apply` restated without the
`dsimp%` in its left-hand side, so that it can be used as a
rewrite on `objEquiv` expressions. -/
lemma prism_objEquiv_δ_apply {m : ℕ}
    (z : (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋m + 1⦌) (j : Fin (m + 2))
    (t : Fin (m + 1)) :
    prodStdSimplex.objEquiv ((Δ[n] ⊗ Δ[1]).δ j z) t =
      prodStdSimplex.objEquiv z (j.succAbove t) :=
  prodStdSimplex.objEquiv_δ_apply z j t

/-- Membership in a product subcomplex from the first component. -/
lemma ofSimplex_le_prod_top_of_fst_mem {m : ℕ}
    {z : (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋m⦌} {S : (Δ[n]).Subcomplex}
    (h : z.1 ∈ S.obj _) :
    Subcomplex.ofSimplex z ≤ S.prod ⊤ := by
  rw [Subcomplex.ofSimplex_le_iff]
  exact ⟨h, Set.mem_univ _⟩

/-- Membership in a product subcomplex from the second component. -/
lemma ofSimplex_le_top_prod_of_snd_mem {m : ℕ}
    {z : (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋m⦌} {T : (Δ[1]).Subcomplex}
    (h : z.2 ∈ T.obj _) :
    Subcomplex.ofSimplex z ≤ (⊤ : (Δ[n]).Subcomplex).prod T := by
  rw [Subcomplex.ofSimplex_le_iff]
  exact ⟨Set.mem_univ _, h⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Omitting a vertex of `τₖ` before the turn (`j < k`) deletes
the first coordinate `j`: the face lies in `∂Δ[n] ⊗ Δ[1]`. -/
lemma prismTau_δ_ofSimplex_le_boundary_prod_top_of_lt
    {k : Fin (n + 1)} {j : Fin (n + 2)} (hjk : j.val < k.val) :
    Subcomplex.ofSimplex ((Δ[n] ⊗ Δ[1] : SSet.{u}).δ j (prismTau n k)) ≤
      (∂Δ[n]).prod ⊤ := by
  apply ofSimplex_le_prod_top_of_fst_mem
  apply mem_boundary_of_forall_ne _ ⟨j.val, by omega⟩
  intro t ht
  have hval : (((Δ[n] ⊗ Δ[1] : SSet.{u}).δ j (prismTau n k)).1 t).val = j.val := by
    rw [ht]
  rw [← prodStdSimplex.objEquiv_apply_fst] at hval
  rw [prism_objEquiv_δ_apply] at hval
  have hiff := (prismTau_objEquiv_fst_val_eq_iff.{u} (k := k)
    (t := j.succAbove t) (i := ⟨j.val, by omega⟩)).1 hval
  rcases hiff with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact absurd (Fin.ext h1) (Fin.succAbove_ne j t)
  · change k.val ≤ j.val at h2
    omega

set_option backward.isDefEq.respectTransparency.types false in
/-- Omitting a vertex of `τₖ` after the turn (`k + 1 < j`)
deletes the first coordinate `j - 1`: the face lies in
`∂Δ[n] ⊗ Δ[1]`. -/
lemma prismTau_δ_ofSimplex_le_boundary_prod_top_of_gt
    {k : Fin (n + 1)} {j : Fin (n + 2)} (hjk : k.val + 1 < j.val) :
    Subcomplex.ofSimplex ((Δ[n] ⊗ Δ[1] : SSet.{u}).δ j (prismTau n k)) ≤
      (∂Δ[n]).prod ⊤ := by
  apply ofSimplex_le_prod_top_of_fst_mem
  apply mem_boundary_of_forall_ne _ ⟨j.val - 1, by omega⟩
  intro t ht
  have hval : (((Δ[n] ⊗ Δ[1] : SSet.{u}).δ j (prismTau n k)).1 t).val =
      j.val - 1 := by
    rw [ht]
  rw [← prodStdSimplex.objEquiv_apply_fst] at hval
  rw [prism_objEquiv_δ_apply] at hval
  have hiff := (prismTau_objEquiv_fst_val_eq_iff.{u} (k := k)
    (t := j.succAbove t) (i := ⟨j.val - 1, by omega⟩)).1 hval
  rcases hiff with ⟨h1, h2⟩ | ⟨h1, -⟩
  · change (j.succAbove t).val = j.val - 1 at h1
    change j.val - 1 ≤ k.val at h2
    omega
  · change (j.succAbove t).val = j.val - 1 + 1 at h1
    have hsj : (j.succAbove t).val = j.val := by omega
    exact absurd (Fin.ext hsj) (Fin.succAbove_ne j t)

end PrismCombinatorics

/-! ## The source-prescribed `Δ[1]`-prism filtration

The decreasing filtration `Gₘ = S₀ ⊔ ⨆_{k ≥ m} ofSimplex τₖ` of
§1 of the header, where
`S₀ = ∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}`. The step
`Gₘ = Gₘ₊₁ ⊔ ofSimplex τₘ` attaches `τₘ` along `Λ[n+1, m]`. -/

section PrismOneSrc

variable {n : ℕ}

/-- The initial subcomplex for the source-prescribed prism:
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}`. -/
noncomputable abbrev prismSrcInitial (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd ∂Δ[n] (stdSimplex.face {0})

/-- The decreasing prism filtration: `S₀` together with the top
simplices `τₖ` for `k ≥ m`. -/
noncomputable def prismSrcFilt (n : ℕ) (m : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  prismSrcInitial n ⊔ ⨆ (k : Fin (n + 1)) (_ : m ≤ k.val),
    Subcomplex.ofSimplex (prismTau n k)

lemma prismSrcInitial_le_prismSrcFilt (m : ℕ) :
    prismSrcInitial n ≤ prismSrcFilt n m :=
  le_sup_left

lemma ofSimplex_prismTau_le_prismSrcFilt {m : ℕ} {k : Fin (n + 1)}
    (h : m ≤ k.val) :
    Subcomplex.ofSimplex (prismTau n k) ≤ prismSrcFilt n m := by
  unfold prismSrcFilt
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le h le_rfl

lemma prismSrcFilt_succ_le (m : ℕ) :
    prismSrcFilt n (m + 1) ≤ prismSrcFilt n m := by
  unfold prismSrcFilt
  apply sup_le le_sup_left
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  refine (le_iSup_of_le k ?_).trans le_sup_right
  exact le_iSup_of_le (Nat.le_trans (Nat.le_succ m) h) le_rfl

/-- One filtration step: `Gₘ = Gₘ₊₁ ⊔ ofSimplex τₘ`. -/
lemma prismSrcFilt_eq_succ_sup {m : ℕ} (hm : m ≤ n) :
    prismSrcFilt n m = prismSrcFilt n (m + 1) ⊔
      Subcomplex.ofSimplex (prismTau n ⟨m, by omega⟩) := by
  apply le_antisymm
  · unfold prismSrcFilt
    apply sup_le (le_sup_left.trans le_sup_left)
    apply iSup_le
    intro k
    apply iSup_le
    intro h
    by_cases hk : k.val = m
    · have hke : k = ⟨m, by omega⟩ := Fin.ext hk
      rw [hke]
      exact le_sup_right
    · refine (le_iSup_of_le k ?_).trans
        (le_sup_right.trans le_sup_left)
      exact le_iSup_of_le (show m + 1 ≤ k.val by omega) le_rfl
  · exact sup_le (prismSrcFilt_succ_le m)
      (ofSimplex_prismTau_le_prismSrcFilt le_rfl)

/-- The top of the decreasing filtration is the initial
subcomplex. -/
lemma prismSrcFilt_top :
    prismSrcFilt n (n + 1) = prismSrcInitial n := by
  refine le_antisymm ?_ le_sup_left
  unfold prismSrcFilt
  refine sup_le le_rfl ?_
  apply iSup_le
  intro k
  apply iSup_le
  intro h
  exfalso
  have h2 := k.isLt
  omega

/-- The bottom of the decreasing filtration is the whole prism
(the `τₖ` are all the nondegenerate top simplices, upstream
`SSet.prodStdSimplex.subcomplex_eq_top_iff`). -/
lemma prismSrcFilt_zero : prismSrcFilt n 0 = ⊤ := by
  refine (prodStdSimplex.subcomplex_eq_top_iff
    (prismSrcFilt n 0) rfl).2 ?_
  intro x hx
  obtain ⟨k, hk⟩ :=
    prodStdSimplex₁.nonDegenerateEquiv.surjective ⟨x, hx⟩
  have hval : prismTau n k = x := congrArg Subtype.val hk
  rw [← hval]
  exact ofSimplex_prismTau_le_prismSrcFilt (Nat.zero_le _) _
    (Subcomplex.mem_ofSimplex_obj _)

/-- The image of the `j`-th face subcomplex under `τₖ`'s
classifying map is the subcomplex generated by the `j`-th face
of `τₖ`. -/
lemma image_face_singleton_compl_prismTauMap (k : Fin (n + 1))
    (j : Fin (n + 2)) :
    (stdSimplex.face {j}ᶜ).image (prismTauMap n k) =
      Subcomplex.ofSimplex
        ((Δ[n] ⊗ Δ[1] : SSet.{u}).δ j (prismTau n k)) := by
  rw [stdSimplex.face_singleton_compl, Subcomplex.image_ofSimplex,
    prismTauMap, prodStdSimplex₁.ι_def,
    yonedaEquiv_symm_app_objEquiv_symm]
  rfl

/-- The diagonal simplex `codimOneSimplex j` does not lie in the
initial subcomplex `∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0}` when its second
coordinates take the value `1` (e.g. `j = k.castSucc`, at the
vertex `(k, 1)`): its first component is the fundamental simplex
of `Δ[n]`, which is not in the boundary. -/
lemma codimOne_notMem_prismSrcInitial {j : Fin (n + 2)}
    {t₀ : Fin (n + 1)}
    (ht₀ : stdSimplex.objMk₁.{u} j t₀ = 1) :
    ((prodStdSimplex₁.codimOneSimplex j).1 :
      (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋n⦌) ∉
      (prismSrcInitial n).obj _ := by
  intro hmem
  have hmem2 := (Subcomplex.mem_unionProd_iff _ _ _).1 hmem
  rcases hmem2 with hsnd | hfst
  · have h1 := (stdSimplex.mem_face_iff _ _).1 hsnd t₀
    rw [codimOne_snd, ht₀] at h1
    simp at h1
  · rw [codimOne_fst] at hfst
    exact stdSimplex.notMem_boundary n hfst

/-- **The attaching horn for the decreasing filtration**: the
preimage of `Gₖ₊₁` under `τₖ` is `Λ[n+1, k]`. One inclusion is
the face analysis (every face but `dₖ` lies in
`∂Δ[n] ⊗ Δ[1]`, in `Δ[n] ⊗ {0}`, or in `τₖ₊₁`); the other is that
the missing diagonal face `dₖ τₖ` is in none of these, by the
range characterizations. -/
lemma prismSrcFilt_preimage_prismTauMap (k : Fin (n + 1)) :
    (prismSrcFilt n (k.val + 1)).preimage (prismTauMap.{u} n k) =
      Λ[n + 1, k.castSucc] := by
  apply le_antisymm
  · rw [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap,
      prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv,
      Subcomplex.ofSimplex_le_iff]
    intro hmem
    unfold prismSrcFilt at hmem
    rw [Subfunctor.max_obj, Set.mem_union] at hmem
    rcases hmem with h0 | hI
    · exact codimOne_notMem_prismSrcInitial (j := k.castSucc)
        (t₀ := ⟨k.val, k.isLt⟩) (by
          rw [stdSimplex.objMk₁_apply]
          simp only [show ¬ ((⟨k.val, k.isLt⟩ : Fin (n + 1)).castSucc <
              k.castSucc) from by simp, ↓reduceIte]) h0
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hI
      obtain ⟨k', hle, hmem'⟩ := hI
      have hle2 : Set.range (prodStdSimplex.objEquiv.{u}
          (prodStdSimplex₁.codimOneSimplex k.castSucc).1) ⊆
          Set.range (prodStdSimplex.objEquiv.{u} (prismTau n k')) :=
        (prodStdSimplex.ofSimplex_le_ofSimplex_iff _ _).1
          ((Subcomplex.ofSimplex_le_iff _ _).2 hmem')
      have hmemK : (⟨k.val, k.isLt⟩, (1 : Fin 2)) ∈ Set.range
          (prodStdSimplex.objEquiv.{u}
            (prodStdSimplex₁.codimOneSimplex k.castSucc).1) :=
        mem_range_codimOne_objEquiv.2 (Or.inr ⟨rfl, le_rfl⟩)
      have hthis := hle2 hmemK
      have hle' : k' ≤ ⟨k.val, k.isLt⟩ := by
        exact
          (prodStdSimplex₁.mem_range_objEquiv_nonDegenerateEquiv₁_iff.{u}
            k' ⟨k.val, k.isLt⟩).1 hthis
      change k'.val ≤ k.val at hle'
      omega
  · rw [horn_eq_iSup]
    apply iSup_le
    rintro ⟨j, hj⟩
    have hj' : j ≠ k.castSucc := by
      simpa using hj
    rw [← Subcomplex.image_le_iff,
      image_face_singleton_compl_prismTauMap]
    by_cases hjk : j.val < k.val
    · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_lt
        hjk).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
          (prismSrcInitial_le_prismSrcFilt _))
    · by_cases hjk2 : k.val + 1 < j.val
      · exact (prismTau_δ_ofSimplex_le_boundary_prod_top_of_gt
          hjk2).trans ((Subcomplex.prod_top_le_unionProd _ _).trans
            (prismSrcInitial_le_prismSrcFilt _))
      · have hne : j.val ≠ k.val := fun hv ↦ hj' (Fin.ext hv)
        have hj_eq : j = k.succ := Fin.ext (by
          show j.val = (k.succ).val
          rw [Fin.val_succ]
          omega)
        subst hj_eq
        rw [prodStdSimplex₁.δ_succ_nonDegenerateEquiv]
        by_cases hkn : k.val = n
        · refine (ofSimplex_le_top_prod_of_snd_mem ?_).trans
            ((Subcomplex.top_prod_le_unionProd _ _).trans
              (prismSrcInitial_le_prismSrcFilt _))
          rw [codimOne_snd, stdSimplex.mem_face_iff]
          intro t
          rw [stdSimplex.objMk₁_apply]
          have ht : t.castSucc < k.succ := by
            rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
            have ht2 := t.isLt
            omega
          simp only [ht, ↓reduceIte, Finset.mem_singleton]
        · have hδ : (Δ[n] ⊗ Δ[1] : SSet.{u}).δ
                (⟨k.val + 1, by omega⟩ : Fin (n + 1)).castSucc
                (prismTau n ⟨k.val + 1, by omega⟩) =
              (prodStdSimplex₁.codimOneSimplex k.succ).1 :=
            prodStdSimplex₁.δ_castSucc_nonDegenerateEquiv _
          rw [← hδ]
          have hmem'' : (Δ[n] ⊗ Δ[1] : SSet.{u}).δ
                (⟨k.val + 1, by omega⟩ : Fin (n + 1)).castSucc
                (prismTau n ⟨k.val + 1, by omega⟩) ∈
              (Subcomplex.ofSimplex
                (prismTau n ⟨k.val + 1, by omega⟩)).obj _ :=
            (Subcomplex.ofSimplex
              (prismTau n ⟨k.val + 1, by omega⟩)).map _
              (Subcomplex.mem_ofSimplex_obj _)
          exact ((Subcomplex.ofSimplex_le_iff _ _).2 hmem'').trans
            (ofSimplex_prismTau_le_prismSrcFilt le_rfl)

/-- The vertical edge of the prism at vertex `0`: the
`1`-simplex `(0,0) ⟶ (0,1)`. This is the special edge of the
last attaching horn `Λ[n+1, 0]`. -/
noncomputable def prismVertZero (n : ℕ) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}) _⦋1⦌ :=
  prodStdSimplex.objEquiv.symm
    ⟨fun t ↦ (0, t), fun _ _ hab ↦ ⟨le_rfl, hab⟩⟩

lemma prismVertZero_fst_apply (t : Fin 2) :
    (prismVertZero n).1 t = 0 :=
  rfl

/-- For `n ≥ 1` the vertical edge at vertex `0` lies in the
initial subcomplex: its first components miss the value `1`. -/
lemma prismVertZero_mem_prismSrcInitial (hn : 1 ≤ n) :
    prismVertZero.{u} n ∈ (prismSrcInitial n).obj _ := by
  refine (Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr ?_)
  refine mem_boundary_of_forall_ne _ ⟨1, by omega⟩ (fun t ht ↦ ?_)
  rw [prismVertZero_fst_apply] at ht
  have hval := congrArg Fin.val ht
  simp at hval

end PrismOneSrc

end SSet

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialNerve/HornThickening/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import MathlibExt.AlgebraicTopology.CategoricalSource.SimplicialThickening
/-!
# The simplicial thickening of a horn

For a linear order `J`, Mathlib's simplicial thickening `SimplicialThickening J` is the simplicial
category `C[Δ^J]`: its mapping simplicial set from `i` to `j` is the nerve of the poset
`Path i j` of subsets of the interval `[i, j]` containing both endpoints, and composition is
union of paths. The `n`-simplices of the simplicial nerve `SimplicialNerve C` of a simplicial
category `C` are the simplicial functors from `SimplicialThickening (ULift (Fin (n + 1)))` to `C`.

Let `J` have a least element `⊥` and a greatest element `⊤`, and let `⊥ < c < ⊤`. The rigidification
`C[Λ^J_c]` of the horn of `Δ^J` opposite `c` is the simplicial subcategory of `C[Δ^J]` with the same
objects and the same mapping simplicial sets, except from `⊥` to `⊤`. There it consists of the
chains of paths that either all omit a common interior vertex other than `c` (they lie in a face of
the horn), or all pass through a common interior vertex (they are composites). Identifying
`N(Path i j)` with a cube `(Δ¹)^{(i, j)}`, this simplicial subset is the cube with its interior
and its face `x_c = 0` removed, so its inclusion is anodyne. Consequently a simplicial functor
`F : C[Λ^J_c] ⥤ C` extends along `C[Λ^J_c] ⥤ C[Δ^J]` as soon as the mapping simplicial set from
`F ⊥` to `F ⊤` is a Kan complex, for instance when all mapping simplicial sets of `C` are Kan
complexes. This is the extension property in the proof that the simplicial nerve of such a category
is a quasicategory.

## Main declarations

* `MathlibExt.CategoricalSource.hornPaths i j c`: the chains of paths from `i` to `j` omitting a common interior vertex
  other than `c` or passing through a common interior vertex.
* `MathlibExt.CategoricalSource.anodyneExtensions_hornPaths_ι`: for `i < c < j` its inclusion into `N(Path i j)` is an
  anodyne extension.
* `MathlibExt.CategoricalSource.HornThickening J c`: the simplicial category `C[Λ^J_c]`, with its inclusion
  `HornThickening.ι J c` into `SimplicialThickening J`.
* `MathlibExt.CategoricalSource.HornThickening.exists_extension`: simplicial functors from `C[Λ^J_c]` whose mapping
  simplicial set from `F ⊥` to `F ⊤` is a Kan complex extend to `C[Δ^J]`.
* `MathlibExt.CategoricalSource.HornThickening.δ`: for `J = Fin (n + 3)` and `j ≠ i`, the inclusion
  `C[Δ^{n+1}] ⥤ C[Λ^{n+2}_i]` of the `j`-th face of the horn.

## Implementation notes

The anodyne property is proved by writing `N(Path i j)` as `N(Set S) ⊗ Δ[1]`, where `S` is the set
of interior vertices other than `c` and the factor `Δ[1]` records whether a path passes through
`c`. Under this isomorphism `hornPaths i j c` becomes the pushout-product of the boundary of the
cube `N(Set S)` with the anodyne extension `Λ[1, 1] ⟶ Δ[1]`, which is anodyne by Mathlib's
`SSet.anodyneExtensions_unionProd_ι`.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.1.5.10 and its proof.
-/

public section

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace MathlibExt.CategoricalSource

open SimplicialThickening (Path chainMk chainMk_obj monotone_chain)

variable {J : Type u} [LinearOrder J] {i j : J}

variable (i j) in
/-- The simplicial subset of the mapping simplicial set `N(Path i j)` of the simplicial thickening
which belongs to the horn opposite `c`: the chains of paths which all omit a common vertex `k`
with `i < k < j` and `k ≠ c`, or which all pass through a common vertex `k` with `i < k < j`. -/
def hornPaths (c : J) : (nerve (Path i j)).Subcomplex where
  obj _ := {x | (∃ k, i < k ∧ k < j ∧ k ≠ c ∧ k ∉ (x.obj (Fin.last _)).I) ∨
    ∃ k, i < k ∧ k < j ∧ k ∈ (x.obj 0).I}
  map _ x hx := by
    rcases hx with ⟨k, h₁, h₂, h₃, h₄⟩ | ⟨k, h₁, h₂, h₄⟩
    · exact Or.inl ⟨k, h₁, h₂, h₃, fun h ↦ h₄ (monotone_chain x (Fin.le_last _) h)⟩
    · exact Or.inr ⟨k, h₁, h₂, monotone_chain x (Fin.zero_le _) h₄⟩

lemma mem_hornPaths_iff (c : J) {n : SimplexCategoryᵒᵖ} (x : (nerve (Path i j)).obj n) :
    x ∈ (hornPaths i j c).obj n ↔
      (∃ k, i < k ∧ k < j ∧ k ≠ c ∧ k ∉ (x.obj (Fin.last _)).I) ∨
        ∃ k, i < k ∧ k < j ∧ k ∈ (x.obj 0).I :=
  Iff.rfl

/-! ### The cube decomposition of `N(Path i j)` -/

namespace hornPaths

/-- The interior vertices of `[i, j]` other than `c`. -/
private abbrev S (i j c : J) := {k : J // i < k ∧ k < j ∧ k ≠ c}

variable (i j) in
/-- The boundary of the cube `N(Set S)`: the chains of subsets which all omit a common element or
all contain a common element. -/
private def cubeBoundary (c : J) : (nerve (Set (S i j c))).Subcomplex where
  obj _ := {y | (∃ k, k ∉ y.obj (Fin.last _)) ∨ ∃ k, k ∈ y.obj 0}
  map _ y hy := by
    rcases hy with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, fun h ↦ hk (leOfHom (y.map (homOfLE (Fin.le_last _))) h)⟩
    · exact Or.inr ⟨k, leOfHom (y.map (homOfLE (Fin.zero_le _))) hk⟩

variable {c : J}

variable (c) in
/-- The interior vertices other than `c` through which a chain of paths passes. -/
private def toCube {d : ℕ} (x : ComposableArrows (Path i j) d) :
    ComposableArrows (Set (S i j c)) d :=
  Monotone.functor (f := fun t ↦ {k : S i j c | k.1 ∈ (x.obj t).I})
    fun _ _ h _ hk ↦ monotone_chain x h hk

private lemma mem_toCube_obj {d : ℕ} (x : ComposableArrows (Path i j) d) (t : Fin (d + 1))
    (k : S i j c) : k ∈ (toCube c x).obj t ↔ k.1 ∈ (x.obj t).I :=
  Iff.rfl

open scoped Classical in
variable (c) in
/-- Whether a chain of paths passes through `c`, as a simplex of `Δ[1]`. -/
private noncomputable def throughVertex {d : ℕ} (x : ComposableArrows (Path i j) d) :
    Fin (d + 1) →o Fin 2 where
  toFun t := if c ∈ (x.obj t).I then 1 else 0
  monotone' _ _ h := by
    dsimp only
    split_ifs with h₁ h₂
    · exact le_rfl
    · exact absurd (monotone_chain x h h₁) h₂
    · exact Fin.zero_le _
    · exact le_rfl

open scoped Classical in
private lemma throughVertex_apply {d : ℕ} (x : ComposableArrows (Path i j) d) (t : Fin (d + 1)) :
    throughVertex c x t = if c ∈ (x.obj t).I then 1 else 0 := rfl

private lemma throughVertex_eq_one_iff {d : ℕ} (x : ComposableArrows (Path i j) d)
    (t : Fin (d + 1)) : throughVertex c x t = 1 ↔ c ∈ (x.obj t).I := by
  rw [throughVertex_apply]
  split_ifs with h <;> simp [h]

variable (hi : i < c) (hj : c < j)

include hi hj in
/-- The path through the vertices of `Y`, and also through `c` if `b` holds. -/
private def pathMk (Y : Set (S i j c)) (b : Prop) : Path i j where
  I := {k | k = i ∨ k = j ∨ (∃ h, (⟨k, h⟩ : S i j c) ∈ Y) ∨ (k = c ∧ b)}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le k hk := by
    rcases hk with rfl | rfl | ⟨h, -⟩ | ⟨rfl, -⟩
    · exact le_rfl
    · exact (hi.trans hj).le
    · exact h.1.le
    · exact hi.le
  le_right k hk := by
    rcases hk with rfl | rfl | ⟨h, -⟩ | ⟨rfl, -⟩
    · exact (hi.trans hj).le
    · exact le_rfl
    · exact h.2.1.le
    · exact hj.le

private lemma mem_pathMk_iff {Y : Set (S i j c)} {b : Prop} {k : J} :
    k ∈ (pathMk hi hj Y b).I ↔ k = i ∨ k = j ∨ (∃ h, (⟨k, h⟩ : S i j c) ∈ Y) ∨ (k = c ∧ b) :=
  Iff.rfl

private lemma pathMk_mono {Y Y' : Set (S i j c)} {b b' : Prop} (hY : Y ⊆ Y') (hb : b → b') :
    (pathMk hi hj Y b).I ⊆ (pathMk hi hj Y' b').I := by
  rintro k (rfl | rfl | ⟨h', hk⟩ | ⟨rfl, hk⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨h', hY hk⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, hb hk⟩))

private lemma monotone_pathMk {d : ℕ} (p : ComposableArrows (Set (S i j c)) d × Δ[1] _⦋d⦌) :
    Monotone fun t ↦ (pathMk hi hj (p.1.obj t) (p.2 t = 1)).I := fun _ _ h ↦
  pathMk_mono hi hj (leOfHom (p.1.map (homOfLE h))) fun hk ↦
    le_antisymm (Fin.le_last _) (hk ▸ SSet.stdSimplex.monotone_apply p.2 h)

/-- A chain of paths is determined by the interior vertices other than `c` through which it passes
and by whether it passes through `c`. -/
private noncomputable def objEquiv (d : ℕ) :
    ComposableArrows (Path i j) d ≃ ComposableArrows (Set (S i j c)) d × Δ[1] _⦋d⦌ where
  toFun x := (toCube c x, SSet.stdSimplex.objMk (throughVertex c x))
  invFun p := chainMk (fun t ↦ pathMk hi hj (p.1.obj t) (p.2 t = 1)) (monotone_pathMk hi hj p)
  left_inv x := by
    refine ComposableArrows.ext (fun t ↦ Path.ext (Set.ext fun k ↦ ?_)) (by subsingleton)
    dsimp only
    rw [chainMk_obj, mem_pathMk_iff, SSet.stdSimplex.objMk_apply]
    constructor
    · rintro (rfl | rfl | ⟨_, hk⟩ | ⟨rfl, hk⟩)
      · exact (x.obj t).left
      · exact (x.obj t).right
      · exact hk
      · exact (throughVertex_eq_one_iff _ _).1 hk
    · intro hk
      by_cases hki : k = i
      · exact Or.inl hki
      by_cases hkj : k = j
      · exact Or.inr (Or.inl hkj)
      have h₁ := lt_of_le_of_ne ((x.obj t).left_le k hk) (Ne.symm hki)
      have h₂ := lt_of_le_of_ne ((x.obj t).le_right k hk) hkj
      by_cases hkc : k = c
      · subst hkc
        exact Or.inr (Or.inr (Or.inr ⟨rfl, (throughVertex_eq_one_iff _ _).2 hk⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨⟨h₁, h₂, hkc⟩, hk⟩))
  right_inv p := by
    refine Prod.ext (ComposableArrows.ext (fun t ↦ Set.ext fun k ↦ ?_) (by subsingleton))
      (SSet.stdSimplex.ext _ _ fun t ↦ ?_)
    · rw [mem_toCube_obj, chainMk_obj, mem_pathMk_iff]
      constructor
      · rintro (h | h | ⟨_, hk⟩ | ⟨h, -⟩)
        · exact absurd h k.2.1.ne'
        · exact absurd h k.2.2.1.ne
        · exact hk
        · exact absurd h k.2.2.2
      · exact fun hk ↦ Or.inr (Or.inr (Or.inl ⟨k.2, hk⟩))
    · have : c ∈ (pathMk hi hj (p.1.obj t) (p.2 t = 1)).I ↔ p.2 t = 1 := by
        rw [mem_pathMk_iff]
        constructor
        · rintro (h | h | ⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hi.ne'
          · exact absurd h hj.ne
          · exact absurd rfl h.2.2
          · exact h
        · exact fun h ↦ Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
      rw [SSet.stdSimplex.objMk_apply, throughVertex_apply]
      simp only [chainMk_obj, this]
      generalize p.2 t = a
      fin_cases a <;> simp

/-- The isomorphism `N(Path i j) ≅ N(Set S) ⊗ Δ[1]`. -/
private noncomputable def cubeIso : nerve (Path i j) ≅ nerve (Set (S i j c)) ⊗ Δ[1] :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (objEquiv hi hj n.unop.len))

private lemma cubeIso_hom_app {d : ℕ} (x : ComposableArrows (Path i j) d) :
    (cubeIso hi hj).hom.app (op ⦋d⦌) x =
      (toCube c x, SSet.stdSimplex.objMk (throughVertex c x)) :=
  rfl

omit hi hj in
private lemma objMk_throughVertex_mem_horn_iff {d : ℕ} (x : ComposableArrows (Path i j) d) :
    SSet.stdSimplex.objMk (n := ⦋1⦌) (m := op ⦋d⦌) (throughVertex c x) ∈
      (Λ[1, 1] : (Δ[1] : SSet.{u}).Subcomplex).obj (op ⦋d⦌) ↔ c ∈ (x.obj 0).I := by
  rw [SSet.mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain rfl : a = 0 := by fin_cases a <;> simp_all
    by_contra hc
    refine h ⟨0, ?_⟩
    rw [SSet.stdSimplex.objMk_apply, throughVertex_apply]
    simp [hc]
  · intro hc
    refine ⟨0, by decide, ?_⟩
    rintro ⟨t, ht⟩
    rw [SSet.stdSimplex.objMk_apply, throughVertex_apply] at ht
    simp [monotone_chain x (Fin.zero_le t) hc] at ht

private lemma mem_hornPaths_iff_cubeIso {d : ℕ} (x : ComposableArrows (Path i j) d) :
    x ∈ (hornPaths i j c).obj (op ⦋d⦌) ↔ (cubeIso hi hj).hom.app (op ⦋d⦌) x ∈
      ((cubeBoundary i j c).unionProd Λ[1, 1]).obj (op ⦋d⦌) := by
  refine (SSet.Subcomplex.mem_unionProd_iff _ _ _).trans ?_ |>.symm
  rw [cubeIso_hom_app]
  dsimp only
  rw [objMk_throughVertex_mem_horn_iff]
  constructor
  · rintro (hc | ⟨⟨k, hk⟩, h⟩ | ⟨⟨k, hk⟩, h⟩)
    · exact Or.inr ⟨c, hi, hj, hc⟩
    · exact Or.inl ⟨k, hk.1, hk.2.1, hk.2.2, h⟩
    · exact Or.inr ⟨k, hk.1, hk.2.1, h⟩
  · rintro (⟨k, h₁, h₂, h₃, h⟩ | ⟨k, h₁, h₂, h⟩)
    · exact Or.inr (Or.inl ⟨⟨k, h₁, h₂, h₃⟩, h⟩)
    · by_cases hkc : k = c
      · subst hkc
        exact Or.inl h
      · exact Or.inr (Or.inr ⟨⟨k, h₁, h₂, hkc⟩, h⟩)

end hornPaths

/-- For `i < c < j`, the inclusion of the paths of the horn opposite `c` into the mapping
simplicial set `N(Path i j)` of the simplicial thickening is an anodyne extension: up to
isomorphism it is the inclusion of the cube `(Δ¹)^{(i, j)}` minus its interior and its face
`x_c = 0`. -/
theorem anodyneExtensions_hornPaths_ι {c : J} (hi : i < c) (hj : c < j) :
    SSet.anodyneExtensions (hornPaths i j c).ι := by
  let e := hornPaths.cubeIso hi hj
  let B := (hornPaths.cubeBoundary i j c).unionProd Λ[1, 1]
  have hB : SSet.anodyneExtensions B.ι :=
    SSet.anodyneExtensions_unionProd_ι _ _ (SSet.anodyneExtensions.horn_ι _)
  have h : hornPaths i j c = B.preimage e.hom := by
    ext ⟨⟨d⟩⟩ x
    exact hornPaths.mem_hornPaths_iff_cubeIso hi hj x
  -- The isomorphism `e` restricts to an isomorphism between `hornPaths i j c` and `B`.
  let φ : (hornPaths i j c : SSet) ≅ (B : SSet) :=
    { hom := SSet.Subcomplex.lift ((hornPaths i j c).ι ≫ e.hom) (by
        rw [← SSet.Subcomplex.image_eq_range, SSet.Subcomplex.image_le_iff, h])
      inv := SSet.Subcomplex.lift (B.ι ≫ e.inv) (by
        rw [← SSet.Subcomplex.image_eq_range, SSet.Subcomplex.image_le_iff, h,
          ← SSet.Subcomplex.preimage_comp, e.inv_hom_id, SSet.Subcomplex.preimage_id])
      hom_inv_id := by
        rw [← cancel_mono (hornPaths i j c).ι]
        simp
      inv_hom_id := by
        rw [← cancel_mono B.ι]
        simp }
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk φ e)).2 hB

/-! ### The simplicial category `C[Λ^J_c]` -/

section Horn

variable [BoundedOrder J]

variable (c : J) in
/-- Simplicial subsets of the mapping simplicial sets of `C[Δ^J]`: all of `N(Path x y)`, except for
`x = ⊥` and `y = ⊤`, where only the paths `hornPaths ⊥ ⊤ c` occur. When `⊥ < c < ⊤` these are the
mapping simplicial sets of the rigidification `C[Λ^J_c]` of the horn of `Δ^J` opposite `c`; the
definition makes sense for every `c`. -/
def hornHom (x y : J) : (SimplicialThickening.mk x ⟶[SSet] SimplicialThickening.mk y).Subcomplex :=
  if x = ⊥ ∧ y = ⊤ then hornPaths x y c else ⊤

@[simp]
lemma hornHom_bot_top (c : J) : hornHom c (⊥ : J) ⊤ = hornPaths ⊥ ⊤ c :=
  ite_eq_left ⟨rfl, rfl⟩

lemma hornHom_eq_top (c : J) {x y : J} (h : ¬(x = ⊥ ∧ y = ⊤)) : hornHom c x y = ⊤ :=
  ite_eq_right h

/-- A chain of paths from `x` to `y` which omits a vertex `k ≠ c` with `x < k < y` belongs to
`hornHom c x y`. -/
lemma mem_hornHom_of_notMem {c x y k : J} {n : SimplexCategoryᵒᵖ}
    {s : (SimplicialThickening.mk x ⟶[SSet] SimplicialThickening.mk y).obj n} (hxk : x < k)
    (hky : k < y) (hkc : k ≠ c) (hk : k ∉ (s.obj (Fin.last _)).I) :
    s ∈ (hornHom c x y).obj n := by
  by_cases hxy : x = ⊥ ∧ y = ⊤
  · obtain ⟨rfl, rfl⟩ := hxy
    rw [hornHom_bot_top]
    exact (mem_hornPaths_iff c s).2 (Or.inl ⟨k, hxk, hky, hkc, hk⟩)
  · rw [hornHom_eq_top c hxy]
    trivial

/-- Away from the pair `(⊥, ⊤)`, the inclusion `hornHom c x y ⟶ N(Path x y)` is an isomorphism. -/
lemma isIso_hornHom_ι (c : J) {x y : J} (h : ¬(x = ⊥ ∧ y = ⊤)) : IsIso (hornHom c x y).ι := by
  rw [hornHom_eq_top c h, ← SSet.Subcomplex.topIso_hom]
  infer_instance

/-- For `⊥ < c < ⊤`, every inclusion `hornHom c x y ⟶ N(Path x y)` of a mapping simplicial set of
`C[Λ^J_c]` into the corresponding one of `C[Δ^J]` is an anodyne extension. -/
lemma anodyneExtensions_hornHom_ι {c : J} (h₁ : ⊥ < c) (h₂ : c < ⊤) (x y : J) :
    SSet.anodyneExtensions (hornHom c x y).ι := by
  by_cases h : x = ⊥ ∧ y = ⊤
  · obtain ⟨rfl, rfl⟩ := h
    rw [hornHom_bot_top]
    exact anodyneExtensions_hornPaths_ι h₁ h₂
  · have := isIso_hornHom_ι c h
    exact SSet.anodyneExtensions.of_isIso _

/-- The composite of two morphisms of `C[Λ^J_c]` in `C[Δ^J]` belongs to `C[Λ^J_c]`: composites
through an interior vertex are in the horn, and composing with a path from `⊥` to `⊥` or from `⊤`
to `⊤` does not change a path. -/
lemma range_eComp_le_hornHom (c x y z : J) :
    SSet.Subcomplex.range (((hornHom c x y).ι ⊗ₘ (hornHom c y z).ι) ≫
      eComp SSet (SimplicialThickening.mk x) (.mk y) (.mk z)) ≤ hornHom c x z := by
  rintro n _ ⟨⟨⟨s, hs⟩, ⟨t, ht⟩⟩, rfl⟩
  by_cases hxz : x = ⊥ ∧ z = ⊤
  swap
  · rw [hornHom_eq_top c hxz]
    trivial
  obtain ⟨rfl, rfl⟩ := hxz
  rw [hornHom_bot_top, mem_hornPaths_iff]
  by_cases hy : y = ⊥
  · subst hy
    rw [hornHom_bot_top, mem_hornPaths_iff] at ht
    rcases ht with ⟨k, h₁, h₂, h₃, h₄⟩ | ⟨k, h₁, h₂, h₄⟩
    · refine Or.inl ⟨k, h₁, h₂, h₃, ?_⟩
      rintro (h | h)
      · exact h₁.ne' (le_antisymm ((s.obj _).le_right k h) bot_le)
      · exact h₄ h
    · exact Or.inr ⟨k, h₁, h₂, Or.inr h₄⟩
  by_cases hy' : y = ⊤
  · subst hy'
    rw [hornHom_bot_top, mem_hornPaths_iff] at hs
    rcases hs with ⟨k, h₁, h₂, h₃, h₄⟩ | ⟨k, h₁, h₂, h₄⟩
    · refine Or.inl ⟨k, h₁, h₂, h₃, ?_⟩
      rintro (h | h)
      · exact h₄ h
      · exact h₂.ne (le_antisymm le_top ((t.obj _).left_le k h))
    · exact Or.inr ⟨k, h₁, h₂, Or.inl h₄⟩
  exact Or.inr ⟨y, bot_lt_iff_ne_bot.2 hy, lt_top_iff_ne_top.2 hy', Or.inl (s.obj 0).right⟩

variable [Nontrivial J]

/-- The identities of `C[Δ^J]` belong to `C[Λ^J_c]`. -/
lemma range_eId_le_hornHom (c x : J) :
    SSet.Subcomplex.range (eId SSet (SimplicialThickening.mk x)) ≤ hornHom c x x := by
  rw [hornHom_eq_top c fun h ↦ bot_ne_top (h.1.symm.trans h.2)]
  exact le_top

end Horn

variable (J) in
/-- The simplicial subcategory of `SimplicialThickening J`, for a nontrivial bounded linear order
`J`, whose mapping simplicial sets are `hornHom c x y`. When `⊥ < c < ⊤` this is the rigidification
`C[Λ^J_c]` of the horn of `Δ^J` opposite `c`; the definition makes sense for every `c`. -/
structure HornThickening (c : J) where
  /-- The underlying element of `J`. -/
  as : J

namespace HornThickening

variable [BoundedOrder J] [Nontrivial J] {c : J}

instance : EnrichedCategory SSet.{u} (HornThickening J c) where
  Hom x y := (hornHom c x.as y.as : SSet)
  id x := SSet.Subcomplex.lift _ (range_eId_le_hornHom c x.as)
  comp x y z := SSet.Subcomplex.lift _ (range_eComp_le_hornHom c x.as y.as z.as)
  id_comp x y := by
    rw [← cancel_mono (hornHom c x.as y.as).ι]
    simp [whiskerRight_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  comp_id x y := by
    rw [← cancel_mono (hornHom c x.as y.as).ι]
    simp [whiskerLeft_comp_tensorHom_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  assoc w x y z := by
    rw [← cancel_mono (hornHom c w.as z.as).ι]
    simp [whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
      ← tensorHom_comp_whiskerRight, ← tensorHom_comp_whiskerLeft, e_assoc]

lemma hom_eq (x y : HornThickening J c) : (x ⟶[SSet] y) = (hornHom c x.as y.as : SSet) :=
  rfl

/-- The identities of `C[Λ^J_c]` are those of `C[Δ^J]`. -/
@[reassoc (attr := simp)]
lemma eId_ι (x : HornThickening J c) :
    eId SSet x ≫ (hornHom c x.as x.as).ι = eId SSet (SimplicialThickening.mk x.as) :=
  SSet.Subcomplex.lift_ι _ (range_eId_le_hornHom c x.as)

/-- The composition of `C[Λ^J_c]` is that of `C[Δ^J]`. -/
@[reassoc (attr := simp)]
lemma eComp_ι (x y z : HornThickening J c) :
    eComp SSet x y z ≫ (hornHom c x.as z.as).ι =
      ((hornHom c x.as y.as).ι ⊗ₘ (hornHom c y.as z.as).ι) ≫
        eComp SSet (SimplicialThickening.mk x.as) (.mk y.as) (.mk z.as) :=
  SSet.Subcomplex.lift_ι _ (range_eComp_le_hornHom c x.as y.as z.as)

variable (J c) in
/-- The inclusion `C[Λ^J_c] ⥤ C[Δ^J]`, the identity on objects and the inclusion `hornHom c x y`
of mapping simplicial sets. -/
@[expose, simps]
def ι : EnrichedFunctor SSet (HornThickening J c) (SimplicialThickening J) where
  obj x := SimplicialThickening.mk x.as
  map x y := (hornHom c x.as y.as).ι
  map_id := eId_ι
  map_comp := eComp_ι

variable (h₁ : ⊥ < c) (h₂ : c < ⊤) {D : Type*} [EnrichedCategory SSet.{u} D]
  (F : EnrichedFunctor SSet (HornThickening J c) D) [SSet.KanComplex (F.obj ⟨⊥⟩ ⟶[SSet] F.obj ⟨⊤⟩)]

open SSet.modelCategoryQuillen in
include h₁ h₂ in
private lemma exists_extMap (x y : J) :
    ∃ g : (SimplicialThickening.mk x ⟶[SSet] .mk y) ⟶ (F.obj ⟨x⟩ ⟶[SSet] F.obj ⟨y⟩),
      (hornHom c x y).ι ≫ g = F.map ⟨x⟩ ⟨y⟩ := by
  by_cases h : x = ⊥ ∧ y = ⊤
  · -- The inclusion is anodyne and the target mapping simplicial set is a Kan complex.
    obtain ⟨rfl, rfl⟩ := h
    have := anodyneExtensions_hornHom_ι h₁ h₂ ⊥ ⊤ _
      (HomotopicalAlgebra.mem_fibrations (Limits.terminal.from (F.obj ⟨⊥⟩ ⟶[SSet] F.obj ⟨⊤⟩)))
    have sq : CommSq (F.map ⟨⊥⟩ ⟨⊤⟩) (hornHom c ⊥ ⊤).ι (Limits.terminal.from _)
      (Limits.terminal.from _) := ⟨Subsingleton.elim _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · -- The inclusion is an isomorphism.
    have := isIso_hornHom_ι c h
    exact ⟨inv (hornHom c x y).ι ≫ F.map ⟨x⟩ ⟨y⟩, IsIso.hom_inv_id_assoc _ _⟩

/-- A chosen extension of the action of `F` on the mapping simplicial set from `x` to `y`. -/
private noncomputable def extMap (x y : J) :
    (SimplicialThickening.mk x ⟶[SSet] .mk y) ⟶ (F.obj ⟨x⟩ ⟶[SSet] F.obj ⟨y⟩) :=
  (exists_extMap h₁ h₂ F x y).choose

private lemma ι_extMap (x y : J) : (hornHom c x y).ι ≫ extMap h₁ h₂ F x y = F.map ⟨x⟩ ⟨y⟩ :=
  (exists_extMap h₁ h₂ F x y).choose_spec

private lemma eId_extMap (x : J) :
    eId SSet (SimplicialThickening.mk x) ≫ extMap h₁ h₂ F x x = eId SSet (F.obj ⟨x⟩) := by
  rw [← eId_ι_assoc, ι_extMap]
  exact F.map_id ⟨x⟩

private lemma eComp_extMap (x y z : J) :
    eComp SSet (SimplicialThickening.mk x) (.mk y) (.mk z) ≫ extMap h₁ h₂ F x z =
      (extMap h₁ h₂ F x y ⊗ₘ extMap h₁ h₂ F y z) ≫ eComp SSet _ _ _ := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rcases lt_trichotomy y z with hyz | rfl | hyz
    · -- For `x < y < z` both factors are entire mapping simplicial sets of `C[Λ^J_c]`, and the
      -- composite is the composition of `C[Λ^J_c]`, which `F` preserves.
      have := isIso_hornHom_ι c (x := x) (y := y) fun h ↦ (h.2 ▸ hyz).not_ge le_top
      have := isIso_hornHom_ι c (x := y) (y := z) fun h ↦ (h.1 ▸ hxy).not_ge bot_le
      rw [← cancel_epi ((hornHom c x y).ι ⊗ₘ (hornHom c y z).ι),
        ← eComp_ι_assoc (x := ⟨x⟩) (y := ⟨y⟩) (z := ⟨z⟩), ι_extMap]
      simp [tensorHom_comp_tensorHom_assoc, ι_extMap]
    · -- Composing with the identity of `y`, which is the only path from `y` to `y`.
      rw [← cancel_epi ((ρ_ _).inv ≫ _ ◁ eId SSet (SimplicialThickening.mk y))]
      simp [reassoc_of% (e_comp_id SSet (SimplicialThickening.mk x) (.mk y)),
        whiskerLeft_comp_tensorHom_assoc, eId_extMap, rightUnitor_inv_comp_tensorHom_assoc]
    · -- There are no paths from `y` to `z < y`.
      ext n ⟨s, t⟩
      exact absurd (Path.le (t.obj 0 : Path y z)) (not_le.2 hyz)
  · -- Composing with the identity of `x`, which is the only path from `x` to `x`.
    rw [← cancel_epi ((λ_ _).inv ≫ eId SSet (SimplicialThickening.mk x) ▷ _)]
    simp [reassoc_of% (e_id_comp SSet (SimplicialThickening.mk x) (.mk z)),
      whiskerRight_comp_tensorHom_assoc, eId_extMap, leftUnitor_inv_comp_tensorHom_assoc]
  · -- There are no paths from `x` to `y < x`.
    ext n ⟨s, t⟩
    exact absurd (Path.le (s.obj 0 : Path x y)) (not_le.2 hxy)

include h₁ h₂ in
/-- A simplicial functor `F` from `C[Λ^J_c]` to a simplicial category extends along the inclusion
`C[Λ^J_c] ⥤ C[Δ^J]` as soon as the mapping simplicial set from `F ⊥` to `F ⊤` is a Kan complex, for
instance when all mapping simplicial sets of the target are Kan complexes. This is the extension
property behind the fact that the simplicial nerve of such a simplicial category is a
quasicategory. -/
theorem exists_extension :
    ∃ G : EnrichedFunctor SSet (SimplicialThickening J) D, (ι J c).comp SSet G = F := by
  refine ⟨{ obj x := F.obj ⟨x.as⟩
            map x y := extMap h₁ h₂ F x.as y.as
            map_id x := eId_extMap h₁ h₂ F x.as
            map_comp x y z := eComp_extMap h₁ h₂ F x.as y.as z.as }, ?_⟩
  -- The objects agree definitionally, so `eqToHom` is the identity.
  refine EnrichedFunctor.ext _ (fun x ↦ by rfl) fun x y ↦ ?_
  exact (Category.comp_id _).trans (ι_extMap h₁ h₂ F x.as y.as)

/-! ### The faces of `C[Λ^{n+2}_i]` -/

section Faces

variable {n : ℕ} {i : Fin (n + 3)}

/-- The simplicial functor `C[Δ^{n+1}] ⥤ C[Δ^{n+2}]` induced by the coface map `δ j` lands in
`C[Λ^{n+2}_i]` for `j ≠ i`. -/
private lemma range_functor_δ_map_le_hornHom {j : Fin (n + 3)} (hj : j ≠ i)
    (a b : SimplicialThickening (ULift.{u} (Fin (n + 2)))) :
    SSet.Subcomplex.range
        ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map a b) ≤
      hornHom (⟨i⟩ : ULift.{u} (Fin (n + 3))) ⟨j.succAbove a.as.down⟩ ⟨j.succAbove b.as.down⟩ := by
  rintro q _ ⟨s, rfl⟩
  have hj' (x : SimplicialThickening (ULift.{u} (Fin (n + 2)))) :
      (⟨j.succAbove x.as.down⟩ : ULift.{u} (Fin (n + 3))) ≠ ⟨j⟩ :=
    fun h ↦ Fin.succAbove_ne j x.as.down (congrArg ULift.down h)
  by_cases hab : (⟨j.succAbove a.as.down⟩ : ULift.{u} (Fin (n + 3))) = ⊥ ∧
      (⟨j.succAbove b.as.down⟩ : ULift.{u} (Fin (n + 3))) = ⊤
  · refine mem_hornHom_of_notMem (lt_of_le_of_ne (hab.1 ▸ bot_le) (hj' a))
      (lt_of_le_of_ne (hab.2 ▸ le_top) (hj' b).symm) (fun h ↦ hj (congrArg ULift.down h)) ?_
    rintro ⟨y, -, hy⟩
    exact Fin.succAbove_ne j y.down (congrArg ULift.down hy)
  · rw [hornHom_eq_top _ hab]
    trivial

/-- The inclusion `C[Δ^{n+1}] ⥤ C[Λ^{n+2}_i]` of the `j`-th face of the horn, for `j ≠ i`: the
simplicial functor `C[Δ^{n+1}] ⥤ C[Δ^{n+2}]` induced by the coface map `δ j`, which lands in the
horn. -/
def δ (j : Fin (n + 3)) (hj : j ≠ i) :
    EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 2))))
      (HornThickening (ULift.{u} (Fin (n + 3))) ⟨i⟩) where
  obj a := ⟨⟨j.succAbove a.as.down⟩⟩
  map a b := SSet.Subcomplex.lift _ (range_functor_δ_map_le_hornHom hj a b)
  map_id a := by
    ext q x
    exact Subtype.ext (congrArg (fun φ ↦ φ.app q x)
      ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map_id a))
  map_comp a b c := by
    ext q x
    exact Subtype.ext (congrArg (fun φ ↦ φ.app q x)
      ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map_comp a b c))

@[simp]
lemma δ_obj (j : Fin (n + 3)) (hj : j ≠ i) (a : SimplicialThickening (ULift.{u} (Fin (n + 2)))) :
    (δ j hj).obj a = ⟨⟨j.succAbove a.as.down⟩⟩ :=
  (rfl)

/-- The face `δ j` of `C[Λ^{n+2}_i]` followed by the inclusion into `C[Δ^{n+2}]` is the simplicial
functor induced by the coface map `δ j`. -/
@[simp]
lemma δ_comp_ι (j : Fin (n + 3)) (hj : j ≠ i) :
    (δ j hj).comp SSet (ι _ _) =
      SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap :=
  EnrichedFunctor.ext _ (fun _ ↦ rfl) fun _ _ ↦ by
    ext
    rfl

end Faces

end HornThickening

end MathlibExt.CategoricalSource

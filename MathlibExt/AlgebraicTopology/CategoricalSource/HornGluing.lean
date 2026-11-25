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
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialNerve/HornThickening/Gluing.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.AlgebraicTopology.CategoricalSource.HornBasic
public import MathlibExt.AlgebraicTopology.CategoricalSource.OrderHomULift
/-!
# Gluing simplicial functors out of the simplicial thickening of a horn

The rigidified inner horn `C[Λ^{n+2}_i]` (`MathlibExt.CategoricalSource.HornThickening`) is glued from its faces
`C[Δ^{n+1}]`: simplicial functors `σ j : C[Δ^{n+1}] ⥤ D` on the faces `j ≠ i` which agree on the
faces of codimension two glue to a simplicial functor `C[Λ^{n+2}_i] ⥤ D`, and simplicial functors
out of `C[Λ^{n+2}_i]` are determined by their restrictions to the faces. This is the step of the
proof that the simplicial nerve of a locally Kan simplicial category is a quasicategory which
turns a horn `Λ[n + 2, i] ⟶ SimplicialNerve D` into a simplicial functor `C[Λ^{n+2}_i] ⥤ D`.

## Main declarations

* `MathlibExt.CategoricalSource.HornThickening.exists_desc`: simplicial functors on the faces `C[Δ^{n+1}]` of an inner
  horn which agree on the faces of codimension two glue to a simplicial functor out of
  `C[Λ^{n+2}_i]`.
* `MathlibExt.CategoricalSource.HornThickening.enrichedFunctor_ext`: simplicial functors out of `C[Λ^{n+2}_i]` are
  determined by their restrictions to the faces.

## Implementation notes

The gluing is done simplex by simplex. A chain of paths of `C[Λ^{n+2}_i]` either omits a vertex
`j ≠ i`, and then lies in the image of the face `C[Δ^{n+1}] ⥤ C[Δ^{n+2}]` induced by `δ j`, where
its value is given by `σ j`, or it passes through an interior vertex and is the composite of two
such chains, where its value is the composite of their values. To compare values with different
sources and targets, the simplices of the mapping simplicial sets of a simplicial category are
recorded together with their sources and targets, as elements of a sigma type `Arr`. The face
functors are injective on these, and the compatibility of the faces `σ j` on faces of codimension
two shows that the values do not depend on the chosen face or decomposition.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.1.5.10.
-/

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe v u

namespace MathlibExt.CategoricalSource.HornThickening

open SimplicialThickening (Path chainMk chainMk_obj monotone_chain)

/-! ### Simplices of mapping simplicial sets together with their endpoints -/

variable {D : Type*} [EnrichedCategory SSet.{v} D] {E : Type*} [EnrichedCategory SSet.{v} E]
  {q q' : SimplexCategoryᵒᵖ}

variable (D q) in
/-- The `q`-simplices of all mapping simplicial sets of `D`, with their sources and targets. -/
private abbrev Arr : Type _ := Σ (a b : D), (a ⟶[SSet] b).obj q

namespace Arr

/-- A `q`-simplex of `a ⟶[SSet] b` given by an element of `Arr D q` with source `a` and target
`b`. -/
private def hom (u : Arr D q) {a b : D} (ha : u.1 = a) (hb : u.2.1 = b) :
    (a ⟶[SSet] b).obj q := by
  subst ha hb
  exact u.2.2

private lemma mk_hom (u : Arr D q) {a b : D} (ha : u.1 = a) (hb : u.2.1 = b) :
    (⟨a, b, u.hom ha hb⟩ : Arr D q) = u := by
  subst ha hb
  rfl

private lemma mk_injective {a b : D} {f g : (a ⟶[SSet] b).obj q}
    (h : (⟨a, b, f⟩ : Arr D q) = ⟨a, b, g⟩) : f = g := by
  simpa using h

private lemma mk_eqToHom {a a' b b' : D} (ha : a = a') (hb : b = b')
    (h : (a ⟶[SSet] b) = (a' ⟶[SSet] b')) (f : (a ⟶[SSet] b).obj q) :
    (⟨a', b', (eqToHom h).app q f⟩ : Arr D q) = ⟨a, b, f⟩ := by
  subst ha hb
  rfl

/-- The action of `SimplexCategoryᵒᵖ` on `Arr D`. -/
private def map (g : q ⟶ q') (u : Arr D q) : Arr D q' :=
  ⟨u.1, u.2.1, (u.1 ⟶[SSet] u.2.1).map g u.2.2⟩

variable (D) in
/-- The identity of `a` as an element of `Arr D q`. -/
private def id (a : D) (q : SimplexCategoryᵒᵖ) : Arr D q :=
  ⟨a, a, (eId SSet a).app q PUnit.unit⟩

open scoped Classical in
/-- The composite of two elements of `Arr D q` (the first one if they are not composable). -/
private noncomputable def comp : Arr D q → Arr D q → Arr D q
  | ⟨a, b, f⟩, ⟨b', c, g⟩ =>
    if h : b' = b then ⟨a, c, (eComp SSet a b c).app q (f, h ▸ g)⟩ else ⟨a, b, f⟩

private lemma comp_mk {a b c : D} (f : (a ⟶[SSet] b).obj q) (g : (b ⟶[SSet] c).obj q) :
    comp ⟨a, b, f⟩ ⟨b, c, g⟩ = ⟨a, c, (eComp SSet a b c).app q (f, g)⟩ := by
  simp [comp]

private lemma comp_fst {u v : Arr D q} (h : u.2.1 = v.1) : (comp u v).1 = u.1 := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, g⟩ := v
  obtain rfl : b = b' := h
  rw [comp_mk]

private lemma comp_snd {u v : Arr D q} (h : u.2.1 = v.1) : (comp u v).2.1 = v.2.1 := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, g⟩ := v
  obtain rfl : b = b' := h
  rw [comp_mk]

private lemma id_comp {a : D} {u : Arr D q} (h : u.1 = a) : comp (id D a q) u = u := by
  obtain ⟨_, b, f⟩ := u
  subst h
  rw [id, comp_mk]
  congr 2
  exact congrArg (fun φ ↦ φ.app q f) (e_id_comp SSet _ b)

private lemma comp_id {b : D} {u : Arr D q} (h : u.2.1 = b) : comp u (id D b q) = u := by
  obtain ⟨a, _, f⟩ := u
  subst h
  rw [id, comp_mk]
  congr 2
  exact congrArg (fun φ ↦ φ.app q f) (e_comp_id SSet a _)

private lemma assoc {u v w : Arr D q} (huv : u.2.1 = v.1) (hvw : v.2.1 = w.1) :
    comp (comp u v) w = comp u (comp v w) := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, g⟩ := v
  obtain ⟨c', d, h⟩ := w
  obtain rfl : b = b' := huv
  obtain rfl : c = c' := hvw
  rw [comp_mk, comp_mk, comp_mk, comp_mk]
  congr 2
  exact congrArg (fun φ ↦ φ.app q (f, (g, h))) (e_assoc SSet a b c d)

private lemma map_comp (g : q ⟶ q') {u v : Arr D q} (h : u.2.1 = v.1) :
    (comp u v).map g = comp (u.map g) (v.map g) := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, f'⟩ := v
  obtain rfl : b = b' := h
  rw [comp_mk]
  simp only [map]
  rw [comp_mk]
  congr 2
  exact (NatTrans.naturality_apply (eComp SSet a b c) g _).symm

end Arr

/-- The action of an enriched functor on `Arr`. -/
private def arrMap (F : EnrichedFunctor SSet.{v} E D) (u : Arr E q) : Arr D q :=
  ⟨F.obj u.1, F.obj u.2.1, (F.map u.1 u.2.1).app q u.2.2⟩

private lemma arrMap_comp_functor {E' : Type*} [EnrichedCategory SSet.{v} E']
    (F : EnrichedFunctor SSet.{v} E E') (G : EnrichedFunctor SSet.{v} E' D) (u : Arr E q) :
    arrMap (F.comp SSet G) u = arrMap G (arrMap F u) :=
  rfl

private lemma arrMap_map (F : EnrichedFunctor SSet.{v} E D) (g : q ⟶ q') (u : Arr E q) :
    arrMap F (u.map g) = (arrMap F u).map g := by
  obtain ⟨a, b, s⟩ := u
  have h := NatTrans.naturality_apply (F.map a b) g s
  exact congrArg (fun x ↦ (⟨F.obj a, F.obj b, x⟩ : Arr D q')) h

private lemma arrMap_id (F : EnrichedFunctor SSet.{v} E D) (a : E) :
    arrMap F (Arr.id E a q) = Arr.id D (F.obj a) q := by
  simp only [arrMap, Arr.id]
  congr 2
  exact congrArg (fun φ ↦ φ.app q PUnit.unit) (F.map_id a)

private lemma arrMap_comp (F : EnrichedFunctor SSet.{v} E D) {u v : Arr E q} (h : u.2.1 = v.1) :
    arrMap F (Arr.comp u v) = Arr.comp (arrMap F u) (arrMap F v) := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, g⟩ := v
  obtain rfl : b = b' := h
  simp only [Arr.comp_mk, arrMap]
  rw [Arr.comp_mk]
  congr 2
  exact congrArg (fun φ ↦ φ.app q (f, g)) (F.map_comp a b c)

/-- Enriched functors with the same action on `Arr` are equal. -/
private lemma ext_arrMap {F G : EnrichedFunctor SSet.{v} E D}
    (h : ∀ (q : SimplexCategoryᵒᵖ) (u : Arr E q), arrMap F u = arrMap G u) : F = G := by
  have hobj (a : E) : F.obj a = G.obj a :=
    congrArg Sigma.fst (h (op ⦋0⦌) (Arr.id E a _))
  refine EnrichedFunctor.ext _ hobj fun a b ↦ ?_
  ext q s
  apply Arr.mk_injective (a := G.obj a) (b := G.obj b)
  refine Eq.trans ?_ (h q ⟨a, b, s⟩)
  simp only [arrMap, NatTrans.comp_app]
  exact Arr.mk_eqToHom (hobj a) (hobj b) _ _

/-! ### Chains of paths in the simplicial thickening -/

section Thickening

variable {J : Type v} [LinearOrder J] {K : Type v} [LinearOrder K]

/-- The `t`-th path of an element of `Arr (SimplicialThickening J) q`. -/
private def paths (u : Arr (SimplicialThickening J) q) (t : Fin (q.unop.len + 1)) : Set J :=
  (u.2.2.obj t).I

private lemma fst_mem_paths (u : Arr (SimplicialThickening J) q) (t : Fin (q.unop.len + 1)) :
    u.1.as ∈ paths u t :=
  (u.2.2.obj t).left

private lemma snd_mem_paths (u : Arr (SimplicialThickening J) q) (t : Fin (q.unop.len + 1)) :
    u.2.1.as ∈ paths u t :=
  (u.2.2.obj t).right

private lemma fst_le_of_mem_paths {u : Arr (SimplicialThickening J) q} {t : Fin (q.unop.len + 1)}
    {z : J} (h : z ∈ paths u t) : u.1.as ≤ z :=
  (u.2.2.obj t).left_le z h

private lemma le_snd_of_mem_paths {u : Arr (SimplicialThickening J) q} {t : Fin (q.unop.len + 1)}
    {z : J} (h : z ∈ paths u t) : z ≤ u.2.1.as :=
  (u.2.2.obj t).le_right z h

private lemma monotone_paths (u : Arr (SimplicialThickening J) q) : Monotone (paths u) :=
  monotone_chain u.2.2

private lemma ext_thickening {u v : Arr (SimplicialThickening J) q} (h₁ : u.1 = v.1)
    (h₂ : u.2.1 = v.2.1) (h : ∀ t, paths u t = paths v t) : u = v := by
  obtain ⟨⟨x⟩, ⟨y⟩, s⟩ := u
  obtain ⟨⟨x'⟩, ⟨y'⟩, s'⟩ := v
  cases h₁
  cases h₂
  obtain rfl : s = s' :=
    ComposableArrows.ext (fun t ↦ Path.ext (h t)) fun _ _ ↦ rfl
  rfl

/-- An element of `Arr (SimplicialThickening J) q` from `x` to `y` given by a monotone family of
subsets containing `x` and `y` and contained in `[x, y]`. -/
private def mkArr {q : SimplexCategoryᵒᵖ} (x y : J) (P : Fin (q.unop.len + 1) → Set J)
    (hP : Monotone P) (hx : ∀ t, x ∈ P t) (hy : ∀ t, y ∈ P t) (hxP : ∀ t, ∀ z ∈ P t, x ≤ z)
    (hPy : ∀ t, ∀ z ∈ P t, z ≤ y) : Arr (SimplicialThickening J) q :=
  ⟨⟨x⟩, ⟨y⟩, chainMk (fun t ↦ ⟨P t, hx t, hy t, hxP t, hPy t⟩) hP⟩

private lemma paths_mkArr {q : SimplexCategoryᵒᵖ} (x y : J) (P : Fin (q.unop.len + 1) → Set J)
    (hP : Monotone P) (hx : ∀ t, x ∈ P t) (hy : ∀ t, y ∈ P t) (hxP : ∀ t, ∀ z ∈ P t, x ≤ z)
    (hPy : ∀ t, ∀ z ∈ P t, z ≤ y) (t : Fin (q.unop.len + 1)) :
    paths (mkArr x y P hP hx hy hxP hPy) t = P t := by
  rw [paths, mkArr, chainMk_obj]

private lemma paths_comp {u v : Arr (SimplicialThickening J) q} (h : u.2.1 = v.1)
    (t : Fin (q.unop.len + 1)) : paths (Arr.comp u v) t = paths u t ∪ paths v t := by
  obtain ⟨a, b, f⟩ := u
  obtain ⟨b', c, g⟩ := v
  obtain rfl : b = b' := h
  rw [Arr.comp_mk]
  rfl

private lemma paths_id (x : SimplicialThickening J) (t : Fin (q.unop.len + 1)) :
    paths (Arr.id _ x q) t = {x.as} :=
  rfl

/-- A chain of paths from a vertex to itself is the identity. -/
private lemma eq_id {u : Arr (SimplicialThickening J) q} (h : u.1 = u.2.1) :
    u = Arr.id _ u.1 q := by
  refine ext_thickening rfl h.symm fun t ↦ ?_
  rw [paths_id]
  ext z
  refine ⟨fun hz ↦ le_antisymm ((le_snd_of_mem_paths hz).trans_eq (congrArg _ h).symm)
    (fst_le_of_mem_paths hz), ?_⟩
  rintro rfl
  exact fst_mem_paths u t

private lemma eq_id_mk {x : J}
    (s : (SimplicialThickening.mk x ⟶[SSet] SimplicialThickening.mk x).obj q) :
    (⟨.mk x, .mk x, s⟩ : Arr (SimplicialThickening J) q) = Arr.id _ (.mk x) q :=
  eq_id rfl

/-- A chain of paths all of which pass through `k` is a composite at `k`. -/
private lemma exists_comp_eq (u : Arr (SimplicialThickening J) q) {k : J}
    (hk : ∀ t, k ∈ paths u t) :
    ∃ u₁ u₂ : Arr (SimplicialThickening J) q, u₁.2.1 = u₂.1 ∧ u₁.2.1.as = k ∧
      Arr.comp u₁ u₂ = u := by
  let u₁ := mkArr u.1.as k (fun t ↦ paths u t ∩ Set.Iic k)
    ((monotone_paths u).inter monotone_const)
    (fun t ↦ ⟨fst_mem_paths u t, Set.mem_Iic.2 (fst_le_of_mem_paths (hk t))⟩)
    (fun t ↦ ⟨hk t, Set.mem_Iic.2 le_rfl⟩) (fun _ _ hz ↦ fst_le_of_mem_paths hz.1)
    (fun _ _ hz ↦ Set.mem_Iic.1 hz.2)
  let u₂ := mkArr k u.2.1.as (fun t ↦ paths u t ∩ Set.Ici k)
    ((monotone_paths u).inter monotone_const) (fun t ↦ ⟨hk t, Set.mem_Ici.2 le_rfl⟩)
    (fun t ↦ ⟨snd_mem_paths u t, Set.mem_Ici.2 (le_snd_of_mem_paths (hk t))⟩)
    (fun _ _ hz ↦ Set.mem_Ici.1 hz.2) (fun _ _ hz ↦ le_snd_of_mem_paths hz.1)
  have h₁ (t) : paths u₁ t = paths u t ∩ Set.Iic k := paths_mkArr ..
  have h₂ (t) : paths u₂ t = paths u t ∩ Set.Ici k := paths_mkArr ..
  have h₁₂ : u₁.2.1 = u₂.1 := rfl
  refine ⟨u₁, u₂, h₁₂, rfl, ext_thickening (Arr.comp_fst h₁₂) (Arr.comp_snd h₁₂) fun t ↦ ?_⟩
  rw [paths_comp h₁₂, h₁, h₂, ← Set.inter_union_distrib_left]
  ext z
  simp

/-- If `u₁ ∘ u₂ = v₁ ∘ v₂` where `u₁` ends at or below the end of `v₁`, then the part of the paths
of `u₂` below the end of `v₁` connects `u₁` to `v₁` and `v₂` to `u₂`. -/
private lemma paths_union_inter_Iic_eq {u₁ u₂ v₁ v₂ : Arr (SimplicialThickening J) q}
    (hu : u₁.2.1 = u₂.1) (hv : v₁.2.1 = v₂.1) (h : Arr.comp u₁ u₂ = Arr.comp v₁ v₂)
    (hle : u₁.2.1.as ≤ v₁.2.1.as) (t : Fin (q.unop.len + 1)) :
    paths u₁ t ∪ (paths u₂ t ∩ Set.Iic v₁.2.1.as) = paths v₁ t ∧
      paths u₂ t ∩ Set.Iic v₁.2.1.as ∪ paths v₂ t = paths u₂ t := by
  have hA (z : J) : z ∈ paths u₁ t ∨ z ∈ paths u₂ t ↔ z ∈ paths v₁ t ∨ z ∈ paths v₂ t := by
    simpa [paths_comp hu, paths_comp hv] using Set.ext_iff.1 (congrArg (paths · t) h) z
  have hA₁ (z : J) (hz : z ∈ paths u₁ t) : z ≤ u₁.2.1.as := le_snd_of_mem_paths hz
  have hB₁ (z : J) (hz : z ∈ paths v₁ t) : z ≤ v₁.2.1.as := le_snd_of_mem_paths hz
  have hB₂ (z : J) (hz : z ∈ paths v₂ t) : v₁.2.1.as ≤ z := hv ▸ fst_le_of_mem_paths hz
  have hk : u₁.2.1.as ∈ paths u₂ t := hu ▸ fst_mem_paths u₂ t
  have hk' : v₁.2.1.as ∈ paths v₁ t := snd_mem_paths v₁ t
  constructor
  · ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro (hz | ⟨hz, hzk'⟩)
      · rcases (hA z).1 (Or.inl hz) with hz' | hz'
        · exact hz'
        · rwa [le_antisymm ((hA₁ z hz).trans hle) (hB₂ z hz')]
      · rcases (hA z).1 (Or.inr hz) with hz' | hz'
        · exact hz'
        · rwa [le_antisymm hzk' (hB₂ z hz')]
    · intro hz
      rcases (hA z).2 (Or.inl hz) with hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr ⟨hz', hB₁ z hz⟩
  · ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic]
    constructor
    · rintro (⟨hz, -⟩ | hz)
      · exact hz
      · rcases (hA z).2 (Or.inr hz) with hz' | hz'
        · rwa [le_antisymm (hA₁ z hz') (hle.trans (hB₂ z hz))]
        · exact hz'
    · intro hz
      by_cases hzk' : z ≤ v₁.2.1.as
      · exact Or.inl ⟨hz, hzk'⟩
      · rcases (hA z).1 (Or.inr hz) with hz' | hz'
        · exact absurd (hB₁ z hz') hzk'
        · exact Or.inr hz'

/-- Two decompositions of a chain of paths as composites at `k ≤ k'` are related by the part of the
chain between `k` and `k'`. -/
private lemma exists_comp_eq_comp {u₁ u₂ v₁ v₂ : Arr (SimplicialThickening J) q}
    (hu : u₁.2.1 = u₂.1) (hv : v₁.2.1 = v₂.1) (h : Arr.comp u₁ u₂ = Arr.comp v₁ v₂)
    (hle : u₁.2.1.as ≤ v₁.2.1.as) :
    ∃ m : Arr (SimplicialThickening J) q, u₁.2.1 = m.1 ∧ m.2.1 = v₂.1 ∧
      Arr.comp u₁ m = v₁ ∧ Arr.comp m v₂ = u₂ := by
  have key := paths_union_inter_Iic_eq hu hv h hle
  have hk' (t) : v₁.2.1.as ∈ paths u₂ t ∩ Set.Iic v₁.2.1.as :=
    ⟨(key t).2 ▸ Set.mem_union_right _ (hv ▸ fst_mem_paths v₂ t), Set.mem_Iic.2 le_rfl⟩
  let m := mkArr u₂.1.as v₁.2.1.as (fun t ↦ paths u₂ t ∩ Set.Iic v₁.2.1.as)
    ((monotone_paths u₂).inter monotone_const)
    (fun t ↦ ⟨fst_mem_paths u₂ t, Set.mem_Iic.2 (hu ▸ hle)⟩) hk'
    (fun _ _ hz ↦ fst_le_of_mem_paths hz.1) (fun _ _ hz ↦ Set.mem_Iic.1 hz.2)
  have hm (t) : paths m t = paths u₂ t ∩ Set.Iic v₁.2.1.as := paths_mkArr ..
  have hum : u₁.2.1 = m.1 := hu
  have hmv : m.2.1 = v₂.1 := hv
  have h₁ : u₁.1 = v₁.1 :=
    (Arr.comp_fst hu).symm.trans ((congrArg (·.1) h).trans (Arr.comp_fst hv))
  have h₂ : v₂.2.1 = u₂.2.1 :=
    (Arr.comp_snd hv).symm.trans ((congrArg (·.2.1) h).symm.trans (Arr.comp_snd hu))
  refine ⟨m, hum, hmv, ?_, ?_⟩
  · refine ext_thickening ((Arr.comp_fst hum).trans h₁) (Arr.comp_snd hum) fun t ↦ ?_
    rw [paths_comp hum, hm, (key t).1]
  · refine ext_thickening (Arr.comp_fst hmv) ((Arr.comp_snd hmv).trans h₂) fun t ↦ ?_
    rw [paths_comp hmv, hm, (key t).2]

/-- The action of `SimplicialThickening.functor f` on chains of paths is the image under `f`. -/
private lemma paths_arrMap_functor (f : K →o J) (u : Arr (SimplicialThickening K) q)
    (t : Fin (q.unop.len + 1)) :
    paths (arrMap (SimplicialThickening.functor f) u) t = f '' paths u t :=
  rfl

private lemma arrMap_functor_injective (f : K →o J) (hf : Function.Injective f) :
    Function.Injective (arrMap (q := q) (SimplicialThickening.functor f)) := by
  intro u v h
  refine ext_thickening (congrArg SimplicialThickening.mk (hf (congrArg (fun w ↦ w.1.as) h)))
    (congrArg SimplicialThickening.mk (hf (congrArg (fun w ↦ w.2.1.as) h))) fun t ↦ ?_
  have := congrArg (paths · t) h
  rwa [paths_arrMap_functor, paths_arrMap_functor, (Set.image_injective.2 hf).eq_iff] at this

/-- A chain of paths whose vertices lie in the range of an order embedding `f` lies in the image of
`SimplicialThickening.functor f`. -/
private lemma exists_arrMap_functor_eq (f : K →o J) (hf : Function.Injective f)
    (u : Arr (SimplicialThickening J) q) (hu : ∀ t, paths u t ⊆ Set.range f) :
    ∃ w, arrMap (SimplicialThickening.functor f) w = u := by
  have hf' := f.monotone.strictMono_of_injective hf
  obtain ⟨a, ha⟩ := hu 0 (fst_mem_paths u 0)
  obtain ⟨b, hb⟩ := hu 0 (snd_mem_paths u 0)
  refine ⟨mkArr a b (fun t ↦ f ⁻¹' paths u t) (Set.monotone_preimage.comp (monotone_paths u))
    (fun t ↦ by simpa [ha] using fst_mem_paths u t) (fun t ↦ by simpa [hb] using snd_mem_paths u t)
    (fun _ _ hz ↦ hf'.le_iff_le.1 (ha ▸ fst_le_of_mem_paths hz))
    (fun _ _ hz ↦ hf'.le_iff_le.1 (hb ▸ le_snd_of_mem_paths hz)), ?_⟩
  refine ext_thickening (congrArg SimplicialThickening.mk ha) (congrArg SimplicialThickening.mk hb)
    fun t ↦ ?_
  rw [paths_arrMap_functor, paths_mkArr, Set.image_preimage_eq_of_subset (hu t)]

end Thickening

/-! ### Faces of the simplicial thickening -/

section Faces

variable {n : ℕ}

/-- The simplicial functor `C[Δ^{n}] ⥤ C[Δ^{n+1}]` induced by the coface map `δ j`. -/
private abbrev δF (j : Fin (n + 2)) :
    EnrichedFunctor SSet.{v} (SimplicialThickening (ULift.{v} (Fin (n + 1))))
      (SimplicialThickening (ULift.{v} (Fin (n + 2)))) :=
  SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap

/-- A chain of paths avoiding the vertex `j` lies in the image of the coface functor `δF j`. -/
private lemma exists_arrMap_δF_eq (j : Fin (n + 2))
    (u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q)
    (hu : ∀ t, ⟨j⟩ ∉ paths u t) : ∃ w, arrMap (δF j) w = u :=
  exists_arrMap_functor_eq _ (ULift.map_injective.2 Fin.succAbove_right_injective) u
    fun t _ hx ↦ OrderHom.mem_range_uliftMap_iff.2 (Fin.exists_succAbove_eq fun h ↦ hu t (h ▸ hx))

private lemma notMem_paths_arrMap_δF (j : Fin (n + 2))
    (w : Arr (SimplicialThickening (ULift.{v} (Fin (n + 1)))) q) (t : Fin (q.unop.len + 1)) :
    ⟨j⟩ ∉ paths (arrMap (δF j) w) t := by
  rw [paths_arrMap_functor]
  rintro ⟨y, -, hy⟩
  exact Fin.succAbove_ne j y.down (congrArg ULift.down hy)

/-- For `j < k`, a chain of paths lying in the faces `j` and `k` comes from the face `{j, k}`. -/
private lemma exists_eq_arrMap_δF_of_lt {j k : Fin (n + 3)} (hjk : j < k)
    {w w' : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q}
    (h : arrMap (δF j) w = arrMap (δF k) w') :
    ∃ z, w = arrMap (δF (k.pred (Fin.ne_zero_of_lt hjk))) z ∧
      w' = arrMap (δF (j.castPred (Fin.ne_last_of_lt hjk))) z := by
  obtain ⟨z, rfl⟩ := exists_arrMap_δF_eq (k.pred (Fin.ne_zero_of_lt hjk)) w fun t hk ↦ by
    have := notMem_paths_arrMap_δF k w' t
    rw [← h, paths_arrMap_functor] at this
    exact this ⟨_, hk, ULift.ext (Fin.succAbove_pred_of_lt _ _ hjk)⟩
  refine ⟨z, rfl, arrMap_functor_injective _
    (ULift.map_injective.2 Fin.succAbove_right_injective) (h.symm.trans ?_)⟩
  rw [← arrMap_comp_functor, ← arrMap_comp_functor, ← SimplicialThickening.functor_comp,
    ← SimplicialThickening.functor_comp]
  -- This is the simplicial identity `δ (k - 1) ≫ δ j = δ j ≫ δ k` (Mathlib's `δ_comp_δ`).
  have hδ := SimplexCategory.δ_comp_δ
    ((Fin.castPred_le_pred_iff (Fin.ne_last_of_lt hjk) (Fin.ne_zero_of_lt hjk)).2 hjk)
  exact congrArg (fun f ↦ arrMap (SimplicialThickening.functor f) z)
    (OrderHom.ext _ _ (funext fun y ↦ ULift.ext (by
      simpa [SimplexCategory.δ] using (congrArg (fun f ↦ f.toOrderHom y.down) hδ).symm)))

end Faces

/-! ### Gluing faces of a horn -/

section Glue

variable {n : ℕ} {i : Fin (n + 3)}

/-- The faces `σ` of a horn in the simplicial nerve agree on the faces of codimension two. -/
private def IsCompat
    (σ : ∀ j, j ≠ i → EnrichedFunctor SSet.{v} (SimplicialThickening (ULift.{v} (Fin (n + 2)))) D) :
    Prop :=
  ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
    (δF (k.pred (Fin.ne_zero_of_lt hjk))).comp SSet.{v} (σ j hj) =
      (δF (j.castPred (Fin.ne_last_of_lt hjk))).comp SSet.{v} (σ k hk)

variable
  (σ : ∀ j, j ≠ i → EnrichedFunctor SSet.{v} (SimplicialThickening (ULift.{v} (Fin (n + 2)))) D)
  (hσ : IsCompat σ) (h₀ : 0 < i)

variable (i) in
/-- A chain of paths of `C[Δ^{n+2}]` lies in a face of the horn opposite `i`. -/
private def InFace (u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q) : Prop :=
  ∃ (j : Fin (n + 3)) (_ : j ≠ i) (w : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q),
    arrMap (δF j) w = u

private lemma inFace_of_notMem {j : Fin (n + 3)} (hj : j ≠ i)
    {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q} (h : ∀ t, ⟨j⟩ ∉ paths u t) :
    InFace i u :=
  let ⟨w, hw⟩ := exists_arrMap_δF_eq j u h
  ⟨j, hj, w, hw⟩

private lemma InFace.map {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (h : InFace i u) (g : q ⟶ q') : InFace i (u.map g) := by
  obtain ⟨j, hj, w, rfl⟩ := h
  exact ⟨j, hj, w.map g, arrMap_map _ _ _⟩

/-- The factors of a composite lying in a face lie in that face. -/
private lemma exists_arrMap_δF_comp {j : Fin (n + 3)}
    {u v : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q} (huv : u.2.1 = v.1)
    {w : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q}
    (h : arrMap (δF j) w = Arr.comp u v) :
    ∃ w₁ w₂, w₁.2.1 = w₂.1 ∧ arrMap (δF j) w₁ = u ∧ arrMap (δF j) w₂ = v ∧
      Arr.comp w₁ w₂ = w := by
  have hu (t) : ⟨j⟩ ∉ paths u t := fun hj ↦ notMem_paths_arrMap_δF j w t
    (h ▸ (paths_comp huv t).symm ▸ Or.inl hj)
  have hv (t) : ⟨j⟩ ∉ paths v t := fun hj ↦ notMem_paths_arrMap_δF j w t
    (h ▸ (paths_comp huv t).symm ▸ Or.inr hj)
  obtain ⟨w₁, rfl⟩ := exists_arrMap_δF_eq j u hu
  obtain ⟨w₂, rfl⟩ := exists_arrMap_δF_eq j v hv
  have h₁₂ : w₁.2.1 = w₂.1 := congrArg SimplicialThickening.mk
    (ULift.ext (Fin.succAbove_right_injective (congrArg (·.as.down) huv)))
  exact ⟨w₁, w₂, h₁₂, rfl, rfl, arrMap_functor_injective _
    (ULift.map_injective.2 Fin.succAbove_right_injective)
    ((arrMap_comp _ h₁₂).trans h.symm)⟩

include hσ in
private lemma arrMap_σ_eq {j k : Fin (n + 3)} (hj : j ≠ i) (hk : k ≠ i)
    {w w' : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q}
    (h : arrMap (δF j) w = arrMap (δF k) w') : arrMap (σ j hj) w = arrMap (σ k hk) w' := by
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · obtain ⟨z, rfl, rfl⟩ := exists_eq_arrMap_δF_of_lt hjk h
    have := hσ j k hj hk hjk
    exact congrArg (fun F ↦ arrMap F z) this
  · rw [arrMap_functor_injective _ (ULift.map_injective.2 Fin.succAbove_right_injective) h]
  · obtain ⟨z, rfl, rfl⟩ := exists_eq_arrMap_δF_of_lt hjk h.symm
    have := hσ k j hk hj hjk
    exact (congrArg (fun F ↦ arrMap F z) this).symm

open scoped Classical in
/-- The value of the face functors `σ` on a chain of paths lying in a face of the horn. -/
private noncomputable def faceVal (u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q) :
    Arr D q :=
  if h : InFace i u then arrMap (σ h.choose h.choose_spec.choose) h.choose_spec.choose_spec.choose
  else Arr.id D ((σ 0 h₀.ne).obj ⟨⟨0⟩⟩) q

include hσ in
private lemma faceVal_arrMap {j : Fin (n + 3)} (hj : j ≠ i)
    (w : Arr (SimplicialThickening (ULift.{v} (Fin (n + 2)))) q) :
    faceVal σ h₀ (arrMap (δF j) w) = arrMap (σ j hj) w := by
  have hu : InFace i (arrMap (δF j) w) := ⟨j, hj, w, rfl⟩
  rw [faceVal, dite_eq_left_of_eq_true (eq_true hu)]
  exact arrMap_σ_eq σ hσ _ _ hu.choose_spec.choose_spec.choose_spec

/-- The objects of the glued functor. -/
private noncomputable def glueObj (x : ULift.{v} (Fin (n + 3))) : D :=
  (faceVal σ h₀ (Arr.id _ (SimplicialThickening.mk x) (op ⦋0⦌))).1

include hσ in
private lemma obj_eq_glueObj {j : Fin (n + 3)} (hj : j ≠ i)
    (a : SimplicialThickening (ULift.{v} (Fin (n + 2)))) :
    (σ j hj).obj a = glueObj σ h₀ ((δF j).obj a).as := by
  have := faceVal_arrMap σ hσ h₀ hj (Arr.id _ a (op ⦋0⦌))
  rw [arrMap_id, arrMap_id] at this
  exact (congrArg Sigma.fst this).symm

include hσ in
private lemma faceVal_fst {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (h : InFace i u) : (faceVal σ h₀ u).1 = glueObj σ h₀ u.1.as := by
  obtain ⟨j, hj, w, rfl⟩ := h
  rw [faceVal_arrMap σ hσ h₀ hj]
  exact obj_eq_glueObj σ hσ h₀ hj _

include hσ in
private lemma faceVal_snd {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (h : InFace i u) : (faceVal σ h₀ u).2.1 = glueObj σ h₀ u.2.1.as := by
  obtain ⟨j, hj, w, rfl⟩ := h
  rw [faceVal_arrMap σ hσ h₀ hj]
  exact obj_eq_glueObj σ hσ h₀ hj _

include hσ in
private lemma faceVal_map {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (h : InFace i u) (g : q ⟶ q') : faceVal σ h₀ (u.map g) = (faceVal σ h₀ u).map g := by
  obtain ⟨j, hj, w, rfl⟩ := h
  rw [← arrMap_map, faceVal_arrMap σ hσ h₀ hj, faceVal_arrMap σ hσ h₀ hj, arrMap_map]

include hσ in
/-- The face values are compatible with composition. -/
private lemma faceVal_comp {u v : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (huv : u.2.1 = v.1) (h : InFace i (Arr.comp u v)) :
    InFace i u ∧ InFace i v ∧
      faceVal σ h₀ (Arr.comp u v) = Arr.comp (faceVal σ h₀ u) (faceVal σ h₀ v) := by
  obtain ⟨j, hj, w, hw⟩ := h
  obtain ⟨w₁, w₂, h₁₂, rfl, rfl, rfl⟩ := exists_arrMap_δF_comp huv hw
  refine ⟨⟨j, hj, w₁, rfl⟩, ⟨j, hj, w₂, rfl⟩, ?_⟩
  rw [← hw, faceVal_arrMap σ hσ h₀ hj, faceVal_arrMap σ hσ h₀ hj, faceVal_arrMap σ hσ h₀ hj,
    arrMap_comp _ h₁₂]

include hσ in
private lemma comp_faceVal_eq_of_le
    {u₁ u₂ v₁ v₂ : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : u₁.2.1 = u₂.1) (hv : v₁.2.1 = v₂.1) (h : Arr.comp u₁ u₂ = Arr.comp v₁ v₂)
    (hle : u₁.2.1.as ≤ v₁.2.1.as) (hv₁ : InFace i v₁) (hu₂ : InFace i u₂) :
    Arr.comp (faceVal σ h₀ u₁) (faceVal σ h₀ u₂) =
      Arr.comp (faceVal σ h₀ v₁) (faceVal σ h₀ v₂) := by
  obtain ⟨m, hum, hmv, h₁, h₂⟩ := exists_comp_eq_comp hu hv h hle
  obtain ⟨hu₁, hm, e₁⟩ := faceVal_comp σ hσ h₀ hum (h₁ ▸ hv₁)
  obtain ⟨-, hv₂, e₂⟩ := faceVal_comp σ hσ h₀ hmv (h₂ ▸ hu₂)
  rw [← h₁, ← h₂, e₁, e₂, Arr.assoc]
  · rw [faceVal_snd σ hσ h₀ hu₁, faceVal_fst σ hσ h₀ hm, hum]
  · rw [faceVal_snd σ hσ h₀ hm, faceVal_fst σ hσ h₀ hv₂, hmv]

include hσ in
private lemma comp_faceVal_eq
    {u₁ u₂ v₁ v₂ : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : u₁.2.1 = u₂.1) (hv : v₁.2.1 = v₂.1) (h : Arr.comp u₁ u₂ = Arr.comp v₁ v₂)
    (hu₁ : InFace i u₁) (hu₂ : InFace i u₂) (hv₁ : InFace i v₁) (hv₂ : InFace i v₂) :
    Arr.comp (faceVal σ h₀ u₁) (faceVal σ h₀ u₂) =
      Arr.comp (faceVal σ h₀ v₁) (faceVal σ h₀ v₂) := by
  rcases le_total u₁.2.1.as v₁.2.1.as with hle | hle
  · exact comp_faceVal_eq_of_le σ hσ h₀ hu hv h hle hv₁ hu₂
  · exact (comp_faceVal_eq_of_le σ hσ h₀ hv hu h.symm hle hu₁ hv₂).symm

variable (i) in
/-- A chain of paths of `C[Δ^{n+2}]` that lies in a face of the horn opposite `i` or is a composite
of two such chains. -/
private def Gluable (u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q) : Prop :=
  InFace i u ∨ ∃ u₁ u₂, u₁.2.1 = u₂.1 ∧ Arr.comp u₁ u₂ = u ∧ InFace i u₁ ∧ InFace i u₂

open scoped Classical in
/-- The value of the glued functor on a chain of paths. -/
private noncomputable def glue (u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q) :
    Arr D q :=
  if InFace i u then faceVal σ h₀ u
  else if h : ∃ u₁ u₂, u₁.2.1 = u₂.1 ∧ Arr.comp u₁ u₂ = u ∧ InFace i u₁ ∧ InFace i u₂ then
    Arr.comp (faceVal σ h₀ h.choose) (faceVal σ h₀ h.choose_spec.choose)
  else faceVal σ h₀ u

private lemma glue_of_inFace {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (h : InFace i u) : glue σ h₀ u = faceVal σ h₀ u :=
  ite_eq_left h

include hσ in
private lemma glue_comp {u₁ u₂ : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : u₁.2.1 = u₂.1) (hu₁ : InFace i u₁) (hu₂ : InFace i u₂) :
    glue σ h₀ (Arr.comp u₁ u₂) = Arr.comp (faceVal σ h₀ u₁) (faceVal σ h₀ u₂) := by
  by_cases hc : InFace i (Arr.comp u₁ u₂)
  · rw [glue_of_inFace σ h₀ hc]
    exact (faceVal_comp σ hσ h₀ hu hc).2.2
  · have hex : ∃ v₁ v₂, v₁.2.1 = v₂.1 ∧ Arr.comp v₁ v₂ = Arr.comp u₁ u₂ ∧ InFace i v₁ ∧
        InFace i v₂ := ⟨u₁, u₂, hu, rfl, hu₁, hu₂⟩
    rw [glue, ite_eq_right hc, dite_eq_left_of_eq_true (eq_true hex)]
    obtain ⟨hv, hvc, hv₁, hv₂⟩ := hex.choose_spec.choose_spec
    exact comp_faceVal_eq σ hσ h₀ hv hu hvc hv₁ hv₂ hu₁ hu₂

include hσ in
private lemma glue_fst {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : Gluable i u) : (glue σ h₀ u).1 = glueObj σ h₀ u.1.as := by
  rcases hu with hu | ⟨u₁, u₂, h₁₂, rfl, hu₁, hu₂⟩
  · rw [glue_of_inFace σ h₀ hu, faceVal_fst σ hσ h₀ hu]
  · rw [glue_comp σ hσ h₀ h₁₂ hu₁ hu₂, Arr.comp_fst (by
      rw [faceVal_snd σ hσ h₀ hu₁, faceVal_fst σ hσ h₀ hu₂, h₁₂]), faceVal_fst σ hσ h₀ hu₁,
      Arr.comp_fst h₁₂]

include hσ in
private lemma glue_snd {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : Gluable i u) : (glue σ h₀ u).2.1 = glueObj σ h₀ u.2.1.as := by
  rcases hu with hu | ⟨u₁, u₂, h₁₂, rfl, hu₁, hu₂⟩
  · rw [glue_of_inFace σ h₀ hu, faceVal_snd σ hσ h₀ hu]
  · rw [glue_comp σ hσ h₀ h₁₂ hu₁ hu₂, Arr.comp_snd (by
      rw [faceVal_snd σ hσ h₀ hu₁, faceVal_fst σ hσ h₀ hu₂, h₁₂]), faceVal_snd σ hσ h₀ hu₂,
      Arr.comp_snd h₁₂]

include hσ in
private lemma glue_map {u : Arr (SimplicialThickening (ULift.{v} (Fin (n + 3)))) q}
    (hu : Gluable i u) (g : q ⟶ q') : glue σ h₀ (u.map g) = (glue σ h₀ u).map g := by
  rcases hu with hu | ⟨u₁, u₂, h₁₂, rfl, hu₁, hu₂⟩
  · rw [glue_of_inFace σ h₀ hu, glue_of_inFace σ h₀ (hu.map g), faceVal_map σ hσ h₀ hu]
  · rw [Arr.map_comp g h₁₂,
      glue_comp σ hσ h₀ (u₁ := u₁.map g) (u₂ := u₂.map g) h₁₂ (hu₁.map g) (hu₂.map g),
      glue_comp σ hσ h₀ h₁₂ hu₁ hu₂, Arr.map_comp g, faceVal_map σ hσ h₀ hu₁,
      faceVal_map σ hσ h₀ hu₂]
    rw [faceVal_snd σ hσ h₀ hu₁, faceVal_fst σ hσ h₀ hu₂, h₁₂]

variable (h₁ : i < Fin.last _)

include hσ h₁ in
private lemma glue_id (x : ULift.{v} (Fin (n + 3))) :
    glue σ h₀ (Arr.id _ (SimplicialThickening.mk x) q) = Arr.id D (glueObj σ h₀ x) q := by
  obtain ⟨j, hj, hxj⟩ : ∃ j, j ≠ i ∧ x.down ≠ j := by
    by_cases hx : x.down = 0
    · exact ⟨Fin.last _, h₁.ne', hx ▸ (Fin.last_pos' ..).ne⟩
    · exact ⟨0, h₀.ne, hx⟩
  obtain ⟨a, rfl⟩ : x ∈ Set.range (SimplexCategory.δ j).toOrderHom.uliftMap :=
    OrderHom.mem_range_uliftMap_iff.2 (Fin.exists_succAbove_eq hxj)
  -- The objects `(δF j).obj ⟨a⟩` and `.mk ((δ j).uliftMap a)` agree by definition of `δF`.
  calc glue σ h₀ (Arr.id _ (.mk ((SimplexCategory.δ j).toOrderHom.uliftMap a)) q)
      = glue σ h₀ (arrMap (δF j) (Arr.id _ ⟨a⟩ q)) := by rw [arrMap_id]; rfl
    _ = arrMap (σ j hj) (Arr.id _ ⟨a⟩ q) := by
      rw [glue_of_inFace σ h₀ ⟨j, hj, _, rfl⟩, faceVal_arrMap σ hσ h₀ hj]
    _ = _ := by rw [arrMap_id, obj_eq_glueObj σ hσ h₀ hj]; rfl

include h₀ h₁ in
/-- Every chain of paths of the horn `C[Λ^{n+2}_i]` lies in a face or is a composite of chains in
faces. -/
private lemma gluable_of_mem {x y : ULift.{v} (Fin (n + 3))}
    {s : (SimplicialThickening.mk x ⟶[SSet] SimplicialThickening.mk y).obj q}
    (hs : s ∈ (hornHom (⟨i⟩ : ULift.{v} (Fin (n + 3))) x y).obj q) :
    Gluable i ⟨.mk x, .mk y, s⟩ := by
  by_cases hx : x = ⊥
  · by_cases hy : y = ⊤
    · subst hx hy
      rw [hornHom_bot_top, mem_hornPaths_iff] at hs
      rcases hs with ⟨k, -, -, hkc, hk⟩ | ⟨k, hk₁, hk₂, hk⟩
      · exact Or.inl (inFace_of_notMem (j := k.down) (fun h ↦ hkc (ULift.ext h))
          fun t ht ↦ hk (monotone_paths _ (Fin.le_last t) ht))
      · obtain ⟨u₁, u₂, hu, hu₁k, hu₁₂⟩ :=
          exists_comp_eq ⟨.mk ⊥, .mk ⊤, s⟩ (k := k) fun t ↦ monotone_paths _ (Fin.zero_le t) hk
        refine Or.inr ⟨u₁, u₂, hu, hu₁₂, inFace_of_notMem (j := Fin.last _) h₁.ne' fun t ht ↦ ?_,
          inFace_of_notMem (j := 0) h₀.ne fun t ht ↦ ?_⟩
        · exact absurd ((le_snd_of_mem_paths ht).trans_eq hu₁k) (not_le.2 hk₂)
        · have := fst_le_of_mem_paths ht
          rw [← hu, hu₁k] at this
          exact absurd this (not_le.2 hk₁)
    · exact Or.inl (inFace_of_notMem (j := Fin.last _) h₁.ne' fun t ht ↦
        hy (top_le_iff.1 (le_snd_of_mem_paths ht)))
  · exact Or.inl (inFace_of_notMem (j := 0) h₀.ne fun t ht ↦
      hx (le_bot_iff.1 (fst_le_of_mem_paths ht)))

include hσ h₁ in
private lemma glue_comp_of_mem {x y z : ULift.{v} (Fin (n + 3))}
    {s : (SimplicialThickening.mk x ⟶[SSet] SimplicialThickening.mk y).obj q}
    {t : (SimplicialThickening.mk y ⟶[SSet] SimplicialThickening.mk z).obj q}
    (hs : s ∈ (hornHom (⟨i⟩ : ULift.{v} (Fin (n + 3))) x y).obj q)
    (ht : t ∈ (hornHom (⟨i⟩ : ULift.{v} (Fin (n + 3))) y z).obj q) :
    glue σ h₀ (Arr.comp ⟨.mk x, .mk y, s⟩ ⟨.mk y, .mk z, t⟩) =
      Arr.comp (glue σ h₀ ⟨.mk x, .mk y, s⟩) (glue σ h₀ ⟨.mk y, .mk z, t⟩) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rcases lt_trichotomy y z with hyz | rfl | hyz
    · have hu : InFace i ⟨.mk x, .mk y, s⟩ := inFace_of_notMem (j := Fin.last _) h₁.ne'
        fun _ h ↦ (not_top_lt ((le_snd_of_mem_paths h).trans_lt hyz))
      have hv : InFace i ⟨.mk y, .mk z, t⟩ := inFace_of_notMem (j := 0) h₀.ne
        fun _ h ↦ (not_lt_bot (hxy.trans_le (fst_le_of_mem_paths h)))
      rw [glue_comp σ hσ h₀ rfl hu hv, glue_of_inFace σ h₀ hu, glue_of_inFace σ h₀ hv]
    · rw [eq_id_mk t, Arr.comp_id (b := SimplicialThickening.mk y) (u := ⟨_, _, s⟩) rfl,
        glue_id σ hσ h₀ h₁,
        Arr.comp_id (glue_snd σ hσ h₀ (gluable_of_mem h₀ h₁ hs))]
    · exact absurd (Path.le (t.obj 0 : Path y z)) (not_le.2 hyz)
  · rw [eq_id_mk s, Arr.id_comp (a := SimplicialThickening.mk x) (u := ⟨_, _, t⟩) rfl,
      glue_id σ hσ h₀ h₁,
      Arr.id_comp (glue_fst σ hσ h₀ (gluable_of_mem h₀ h₁ ht))]
  · exact absurd (Path.le (s.obj 0 : Path x y)) (not_le.2 hxy)

/-- The action of the glued functor on mapping simplicial sets. -/
private noncomputable def glueMap (x y : ULift.{v} (Fin (n + 3))) :
    (hornHom (⟨i⟩ : ULift.{v} (Fin (n + 3))) x y : SSet.{v}) ⟶
      (glueObj σ h₀ x ⟶[SSet] glueObj σ h₀ y) where
  app q := ↾fun s ↦ (glue σ h₀ ⟨.mk x, .mk y, s.1⟩).hom
    (glue_fst σ hσ h₀ (gluable_of_mem h₀ h₁ s.2)) (glue_snd σ hσ h₀ (gluable_of_mem h₀ h₁ s.2))
  naturality q q' g := by
    ext s
    apply Arr.mk_injective (a := glueObj σ h₀ x) (b := glueObj σ h₀ y)
    refine (Arr.mk_hom _ _ _).trans ((glue_map σ hσ h₀ (gluable_of_mem h₀ h₁ s.2) g).trans ?_)
    exact congrArg (Arr.map g) (Arr.mk_hom _ _ _).symm

private lemma mk_glueMap_app (x y : ULift.{v} (Fin (n + 3)))
    (s : (hornHom (⟨i⟩ : ULift.{v} (Fin (n + 3))) x y : SSet.{v}).obj q) :
    (⟨glueObj σ h₀ x, glueObj σ h₀ y, (glueMap σ hσ h₀ h₁ x y).app q s⟩ : Arr D q) =
      glue σ h₀ ⟨.mk x, .mk y, s.1⟩ :=
  Arr.mk_hom _ _ _

/-- The simplicial functor `C[Λ^{n+2}_i] ⥤ D` glued from the faces `σ`. -/
private noncomputable def glueFunctor :
    EnrichedFunctor SSet.{v} (HornThickening (ULift.{v} (Fin (n + 3))) ⟨i⟩) D where
  obj x := glueObj σ h₀ x.as
  map x y := glueMap σ hσ h₀ h₁ x.as y.as
  map_id x := by
    ext q ⟨⟩
    apply Arr.mk_injective (a := glueObj σ h₀ x.as) (b := glueObj σ h₀ x.as)
    exact (mk_glueMap_app σ hσ h₀ h₁ _ _ _).trans (glue_id σ hσ h₀ h₁ x.as)
  map_comp x y z := by
    ext q ⟨s, t⟩
    apply Arr.mk_injective (a := glueObj σ h₀ x.as) (b := glueObj σ h₀ z.as)
    refine (mk_glueMap_app σ hσ h₀ h₁ _ _ _).trans ?_
    refine ((congrArg (glue σ h₀) (Arr.comp_mk s.1 t.1).symm).trans
      (glue_comp_of_mem σ hσ h₀ h₁ s.2 t.2)).trans ?_
    rw [← mk_glueMap_app σ hσ h₀ h₁ _ _ s, ← mk_glueMap_app σ hσ h₀ h₁ _ _ t, Arr.comp_mk]
    rfl

end Glue

/-- The inclusion `C[Λ^J_c] ⥤ C[Δ^J]` is injective on simplices of mapping simplicial sets. -/
private lemma arrMap_ι_injective {J : Type v} [LinearOrder J] [BoundedOrder J] [Nontrivial J]
    {c : J} : Function.Injective (arrMap (q := q) (ι J c)) := by
  rintro ⟨⟨x⟩, ⟨y⟩, s⟩ ⟨⟨x'⟩, ⟨y'⟩, s'⟩ h
  obtain rfl : x = x' := congrArg (fun w ↦ w.1.as) h
  obtain rfl : y = y' := congrArg (fun w ↦ w.2.1.as) h
  obtain rfl : s = s' := Subtype.ext (Arr.mk_injective h)
  rfl

end MathlibExt.CategoricalSource.HornThickening

public section

namespace MathlibExt.CategoricalSource.HornThickening

variable {n : ℕ} {i : Fin (n + 3)}

variable (h₀ : 0 < i) (h₁ : i < Fin.last _) {D : Type*} [EnrichedCategory SSet.{u} D]

include h₀ h₁ in
/-- Simplicial functors `σ j : C[Δ^{n+1}] ⥤ D` on the faces `j ≠ i` of an inner horn which agree on
the faces of codimension two glue to a simplicial functor `F : C[Λ^{n+2}_i] ⥤ D` with faces `σ`. The
compatibility condition is the one of `SSet.horn.IsCompatible`. -/
theorem exists_desc
    (σ : ∀ j, j ≠ i → EnrichedFunctor SSet.{u} (SimplicialThickening (ULift.{u} (Fin (n + 2)))) D)
    (hσ : ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      (SimplicialThickening.functor
        (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk))).toOrderHom.uliftMap).comp SSet
          (σ j hj) =
        (SimplicialThickening.functor
          (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk))).toOrderHom.uliftMap).comp SSet
            (σ k hk)) :
    ∃ F : EnrichedFunctor SSet.{u} (HornThickening (ULift.{u} (Fin (n + 3))) ⟨i⟩) D,
      ∀ j hj, (δ j hj).comp SSet F = σ j hj := by
  refine ⟨glueFunctor σ hσ h₀ h₁, fun j hj ↦ ext_arrMap fun q w ↦ ?_⟩
  refine (mk_glueMap_app σ hσ h₀ h₁ _ _ _).trans ?_
  -- The underlying chain of paths of the image of `w` in `C[Λ^{n+2}_i]` is its image under `δF j`.
  have h : arrMap ((δ j hj).comp SSet (ι _ _)) w = arrMap (δF j) w := by rw [δ_comp_ι]
  exact ((congrArg (glue σ h₀) h).trans (glue_of_inFace σ h₀ ⟨j, hj, w, rfl⟩)).trans
    (faceVal_arrMap σ hσ h₀ hj w)

include h₀ h₁ in
/-- Simplicial functors out of `C[Λ^{n+2}_i]` which agree on all faces `δ j`, `j ≠ i`, of the inner
horn are equal. Together with `exists_desc`, this says that `C[Λ^{n+2}_i]` is glued from its faces.
-/
theorem enrichedFunctor_ext
    {F G : EnrichedFunctor SSet.{u} (HornThickening (ULift.{u} (Fin (n + 3))) ⟨i⟩) D}
    (h : ∀ j hj, (δ j hj).comp SSet F = (δ j hj).comp SSet G) : F = G := by
  -- A chain of paths lying in a face is the image of a chain of paths of that face.
  have hface {q} {v : Arr (SimplicialThickening (ULift.{u} (Fin (n + 3)))) q} (hv : InFace i v) :
      ∃ u, arrMap (ι _ _) u = v ∧ arrMap F u = arrMap G u := by
    obtain ⟨j, hj, w, rfl⟩ := hv
    refine ⟨arrMap (δ j hj) w, ?_, ?_⟩
    · rw [← arrMap_comp_functor, δ_comp_ι]
    · rw [← arrMap_comp_functor, ← arrMap_comp_functor, h j hj]
  refine ext_arrMap fun q u ↦ ?_
  rcases gluable_of_mem h₀ h₁ u.2.2.2 with hu | ⟨v₁, v₂, h₁₂, hv, hv₁, hv₂⟩
  · obtain ⟨u', hu', e⟩ := hface hu
    rwa [← arrMap_ι_injective hu']
  · obtain ⟨u₁, rfl, e₁⟩ := hface hv₁
    obtain ⟨u₂, rfl, e₂⟩ := hface hv₂
    have h₁₂' : u₁.2.1 = u₂.1 := congrArg HornThickening.mk (congrArg SimplicialThickening.as h₁₂)
    rw [← arrMap_ι_injective ((arrMap_comp _ h₁₂').trans hv), arrMap_comp _ h₁₂',
      arrMap_comp _ h₁₂', e₁, e₂]

end MathlibExt.CategoricalSource.HornThickening

end

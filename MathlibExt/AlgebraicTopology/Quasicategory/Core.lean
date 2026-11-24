/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
public import MathlibExt.CategoryTheory.Subfunctor.PreimagePullback
public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The equivalence-edge core of a simplicial set

For a simplicial set `X`, the *core* `SSet.core X` is the subcomplex
spanned by the simplices all of whose edges are equivalences in the
sense of `SSet.Edge.IsEquivalence`. A simplex `x : X _⦋n⦌` lies in the
core when, for every map `φ : ⦋1⦌ ⟶ ⦋n⦌` in the simplex category, the
edge `Edge.mk' (X.map φ.op x)` is an equivalence. Quantifying over all
such `φ`, rather than only the injective ones, makes stability under
simplicial operators formal (as for `SSet.Subcomplex.full`); the
constant maps contribute only degenerate identity edges, and
`mem_core_obj_iff_forall_edge` shows that it is enough to test the
vertex pairs `a ≤ b` through `stdSimplex.edge`. For an arbitrary
simplicial set the core need not be a Kan complex: for example, a
simplicial sphere such as `Δ[2]/∂Δ[2]` has only degenerate edges, so
its core is itself, yet it is not a Kan complex. The core is the
maximal Kan subcomplex when `X` is a quasicategory; that
`SSet.KanComplex (core X : SSet)` holds then is proved later in this
package (see "Not proved in this file").

The main results are:

* membership characterizations: at vertices
  (`mem_core_obj_zero`, `core_obj_zero`), at `1`-simplices
  (`mem_core_obj_one_iff`), pairwise
  (`mem_core_obj_iff_forall_edge`), and maximality (`le_core_iff`);
* functoriality: every map `f : X ⟶ Y` restricts to the cores
  (`core_le_preimage`, `core.map`);
* if `X` is a Kan complex then `core X = ⊤`
  (`core_eq_top_of_kanComplex`), using the inverse structure on edges
  of a Kan complex from the fundamental-groupoid API;
* unconditionally, the inclusion `core X ↪ X` has the right lifting
  property against every horn `Λ[n + 2, i]` in dimension at least `2`
  (`hasLiftingProperty_horn_core_ι`); in particular it is an inner
  fibration, and the core of a quasicategory is a quasicategory;
* the nerve gate: an `n`-simplex of `nerve C` lies in
  `core (nerve C)` if and only if it is a chain of isomorphisms, in
  all-pairs form (`mem_core_nerve_iff_forall_map'_isIso`) and in
  successive form (`mem_core_nerve_iff_forall_succ_map'_isIso`).

## Not proved in this file

* `KanComplex (core X : SSet)` for a quasicategory `X` is not proved
  in this file; it is proved in
  `MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral`
  as `SSet.kanComplex_core_of_quasicategory` (also an instance),
  from Joyal's special outer horn filling in all dimensions
  (`SSet.hasSpecialOuterHornFilling_of_quasicategory`, packet T21)
  applied to the reduction
  `SSet.kanComplex_core_of_special_horn_filling` of
  `MathlibExt.AlgebraicTopology.Quasicategory.CoreKan`.

## TODO
* TODO(T04): promote the simplex-level nerve gate to an isomorphism
  `(core (nerve C) : SSet) ≅ nerve (CategoryTheory.Core C)` induced
  by `nerveMap (CategoryTheory.Core.inclusion C)`. The
  characterizations `mem_core_nerve_iff_forall_map'_isIso` and
  `mem_core_nerve_iff_forall_succ_map'_isIso` are the simplex-level
  content of that isomorphism.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace SSet

variable {X Y : SSet.{u}}

namespace Edge

variable {x₀ x₁ y₀ y₁ : X _⦋0⦌}

/-- If two edges have the same underlying `1`-simplex, then the
equivalence property of one of them transfers to the other: the
`1`-simplex determines both endpoints, so the two edges are in fact
equal after identifying the endpoints. -/
theorem IsEquivalence.of_edge_eq {e : Edge x₀ x₁} {e' : Edge y₀ y₁}
    (h : e.IsEquivalence) (he : e.edge = e'.edge) : e'.IsEquivalence := by
  have h₀ : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, he]
  have h₁ : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, he]
  subst h₀
  subst h₁
  exact Edge.ext he ▸ h

/-- Two edges with the same underlying `1`-simplex are either both
equivalences or both not equivalences. -/
theorem isEquivalence_iff_of_edge_eq {e : Edge x₀ x₁} {e' : Edge y₀ y₁}
    (he : e.edge = e'.edge) : e.IsEquivalence ↔ e'.IsEquivalence :=
  ⟨fun h ↦ h.of_edge_eq he, fun h ↦ h.of_edge_eq he.symm⟩

/-- Every edge of a Kan complex is an equivalence, via the inverse
structure supplied by the fundamental-groupoid API for Kan
complexes. -/
theorem isEquivalence_of_kanComplex [KanComplex X] (e : Edge x₀ x₁) :
    e.IsEquivalence :=
  e.invStruct.isEquivalence

end Edge

/-- The edge cut out by a degenerate `1`-simplex `X.σ 0 x` is an
equivalence: it is the identity edge. -/
private theorem isEquivalence_mk'_map_σ_zero (x : X _⦋0⦌) :
    (Edge.mk' (X.map (SimplexCategory.σ (0 : Fin 1)).op x)).IsEquivalence :=
  (Edge.isEquivalence_id x).of_edge_eq rfl

/-- The edge of a simplex cut out by a constant map `⦋1⦌ ⟶ Δ` is an
equivalence: the map factors through `⦋0⦌`, so the `1`-simplex is a
degeneracy of a vertex. -/
private theorem isEquivalence_mk'_map_const {Δ : SimplexCategory}
    (x : X.obj (op Δ)) (i : Fin (Δ.len + 1)) :
    (Edge.mk' (X.map (SimplexCategory.const ⦋1⦌ Δ i).op x)).IsEquivalence := by
  have hσ : SimplexCategory.σ (0 : Fin 1) =
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0 :=
    SimplexCategory.eq_const_to_zero _
  have hφ : SimplexCategory.const ⦋1⦌ Δ i =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.const ⦋0⦌ Δ i := by
    rw [hσ]
    exact (SimplexCategory.const_fac_thru_zero ⦋1⦌ Δ i).symm
  rw [hφ, op_comp, X.map_comp]
  exact
    isEquivalence_mk'_map_σ_zero (X.map (SimplexCategory.const ⦋0⦌ Δ i).op x)

/-- The *core* of a simplicial set `X`: the subcomplex of simplices
whose every edge is an equivalence. Precisely, a simplex
`x : X.obj Δ` belongs to `core X` when for every map
`φ : ⦋1⦌ ⟶ Δ.unop`, the edge `Edge.mk' (X.map φ.op x)` cut out by
`φ` is an `Edge.IsEquivalence`.

Quantifying over all `φ` (not only injective ones) is the formulation
the `SSet.Edge` API supports best: stability under `X.map f` is then
formal, the non-injective maps contribute only degenerate identity
edges (`isEquivalence_mk'_map_const`), and
`mem_core_obj_iff_forall_edge` recovers the injective vertex-pair
formulation. -/
def core (X : SSet.{u}) : X.Subcomplex where
  obj Δ := {x | ∀ φ : ⦋1⦌ ⟶ Δ.unop, (Edge.mk' (X.map φ.op x)).IsEquivalence}
  map {Δ Δ'} f x hx φ := by
    have h := hx (φ ≫ f.unop)
    rwa [op_comp, X.map_comp] at h

/-- A simplex lies in the core if and only if every edge cut out by a
map `⦋1⦌ ⟶ Δ.unop` is an equivalence. This is the definition of
`core`. -/
@[simp]
lemma mem_core_obj_iff {Δ : SimplexCategoryᵒᵖ} {x : X.obj Δ} :
    x ∈ (core X).obj Δ ↔
      ∀ φ : ⦋1⦌ ⟶ Δ.unop, (Edge.mk' (X.map φ.op x)).IsEquivalence :=
  Iff.rfl

/-- Every vertex lies in the core: the only maps `⦋1⦌ ⟶ ⦋0⦌` are
constant, and they cut out degenerate identity edges. -/
theorem mem_core_obj_zero (x : X _⦋0⦌) : x ∈ (core X).obj (op ⦋0⦌) := by
  intro φ
  rw [SimplexCategory.eq_const_to_zero φ]
  exact isEquivalence_mk'_map_const x 0

/-- The core has the same vertices as the ambient simplicial set. -/
@[simp]
lemma core_obj_zero (X : SSet.{u}) : (core X).obj (op ⦋0⦌) = Set.univ :=
  Set.eq_univ_of_forall mem_core_obj_zero

/-- A `1`-simplex lies in the core if and only if the edge it
defines is an equivalence. -/
lemma mem_core_obj_one_iff {s : X _⦋1⦌} :
    s ∈ (core X).obj (op ⦋1⦌) ↔ (Edge.mk' s).IsEquivalence := by
  constructor
  · intro h
    have h1 := h (𝟙 ⦋1⦌)
    rwa [op_id, X.map_id] at h1
  · intro h φ
    rcases SimplexCategory.eq_of_one_to_one φ with ⟨a, rfl⟩ | rfl
    · exact isEquivalence_mk'_map_const s a
    · rwa [op_id, X.map_id]

/-- Pairwise characterization of the core: an `n`-simplex lies in
the core if and only if the edge between any two vertices `a ≤ b`
(in the sense of `stdSimplex.edge`) is an equivalence. -/
lemma mem_core_obj_iff_forall_edge {n : ℕ} {x : X _⦋n⦌} :
    x ∈ (core X).obj (op ⦋n⦌) ↔ ∀ (a b : Fin (n + 1)) (hab : a ≤ b),
      (Edge.mk' (X.map
        (stdSimplex.objEquiv (stdSimplex.edge.{u} n a b hab)).op x)).IsEquivalence := by
  refine ⟨fun h a b hab ↦ h _, fun h φ ↦ ?_⟩
  have hab : φ.toOrderHom 0 ≤ φ.toOrderHom 1 :=
    φ.toOrderHom.monotone (Fin.zero_le 1)
  have hφ : stdSimplex.objEquiv
      (stdSimplex.edge.{u} n (φ.toOrderHom 0) (φ.toOrderHom 1) hab) = φ :=
    SimplexCategory.Hom.ext_one_left _ _
  have key := h _ _ hab
  rwa [hφ] at key

/-- The core is the largest subcomplex all of whose `1`-simplices
are equivalences: a subcomplex is contained in the core if and only
if every one of its `1`-simplices defines an equivalence edge. -/
lemma le_core_iff (A : X.Subcomplex) :
    A ≤ core X ↔ ∀ s ∈ A.obj (op ⦋1⦌), (Edge.mk' s).IsEquivalence := by
  constructor
  · intro h s hs
    exact mem_core_obj_one_iff.mp (h _ hs)
  · intro h Δ x hx φ
    exact h _ (A.map φ.op hx)

section Functoriality

variable (f : X ⟶ Y)

/-- The core of `X` is contained in the preimage of the core of `Y`
along any map `f : X ⟶ Y`, because equivalences are preserved by
simplicial maps. -/
lemma core_le_preimage : core X ≤ (core Y).preimage f := by
  intro Δ x hx φ
  have hnat : Y.map φ.op (f.app Δ x) = f.app (op ⦋1⦌) (X.map φ.op x) :=
    (NatTrans.naturality_apply f φ.op x).symm
  rw [hnat]
  exact ((hx φ).map f).of_edge_eq (by simp [Edge.map_edge])

/-- A map `f : X ⟶ Y` of simplicial sets restricts to a map of
cores. -/
def core.map : (core X : SSet.{u}) ⟶ (core Y : SSet.{u}) :=
  Subcomplex.homOfLE (core_le_preimage f) ≫ (core Y).fromPreimage f

/-- The map induced on cores is compatible with the inclusions
into `X` and `Y`. -/
@[reassoc (attr := simp)]
lemma core.map_ι : core.map f ≫ (core Y).ι = (core X).ι ≫ f := by
  simp [core.map]

/-- `SSet.core.map` preserves identities. -/
@[simp]
theorem core.map_id (X : SSet.{u}) :
    core.map (𝟙 X) = 𝟙 (core X : SSet.{u}) := by
  apply (cancel_mono (core X).ι).mp
  rw [core.map_ι, Category.comp_id, Category.id_comp]

/-- `SSet.core.map` preserves composition. -/
@[simp]
theorem core.map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    core.map (f ≫ g) = core.map f ≫ core.map g := by
  apply (cancel_mono (core Z).ι).mp
  rw [core.map_ι, Category.assoc, core.map_ι, ← Category.assoc,
    ← Category.assoc, core.map_ι]

end Functoriality

/-- A simplicial map whose homotopy functor reflects isomorphisms detects
exactly the simplices in the equivalence-edge core. -/
theorem core_eq_preimage_of_reflectsIsomorphisms (f : X ⟶ Y)
    [(mapHomotopyCategory f).ReflectsIsomorphisms] :
    core X = (core Y).preimage f := by
  apply le_antisymm (core_le_preimage f)
  intro d x hx φ
  have hnat : Y.map φ.op (f.app d x) =
      f.app (op ⦋1⦌) (X.map φ.op x) :=
    (NatTrans.naturality_apply f φ.op x).symm
  have hy := hx φ
  rw [hnat] at hy
  let e := Edge.mk' (X.map φ.op x)
  have he : (e.map f).IsEquivalence :=
    hy.of_edge_eq (by simp [e, Edge.map_edge])
  have : IsIso ((mapHomotopyCategory f).map (HomotopyCategory.homMk e)) := by
    rw [mapHomotopyCategory_map_homMk]
    exact he
  exact isIso_of_reflects_iso (HomotopyCategory.homMk e) (mapHomotopyCategory f)

/-- The core inclusion square of a conservative homotopy functor is a
literal pullback. No quasicategory assumption is needed. -/
theorem core.isPullback_of_reflectsIsomorphisms (f : X ⟶ Y)
    [(mapHomotopyCategory f).ReflectsIsomorphisms] :
    IsPullback (core X).ι (core.map f) f (core Y).ι := by
  have heq := core_eq_preimage_of_reflectsIsomorphisms f
  have h : IsPullback ((core Y).preimage f).ι
      ((core Y).fromPreimage f) f (core Y).ι :=
    CategoryTheory.Subfunctor.preimage_isPullback (core Y) f
  apply h.of_iso' (Subcomplex.eqToIso heq) (Iso.refl X)
    (Iso.refl (core Y : SSet.{u})) (Iso.refl Y)
  · simp only [Iso.refl_hom, Category.comp_id]
    change Subcomplex.homOfLE heq.le ≫ ((core Y).preimage f).ι = (core X).ι
    exact Subcomplex.homOfLE_ι heq.le
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp
  · simp


/-- The core of a Kan complex is the whole simplicial set: every
edge of a Kan complex is an equivalence. -/
theorem core_eq_top_of_kanComplex (X : SSet.{u}) [KanComplex X] :
    core X = ⊤ := by
  ext Δ x
  simp only [mem_core_obj_iff, Subfunctor.top_obj, Set.mem_univ, iff_true]
  intro φ
  exact Edge.isEquivalence_of_kanComplex _

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- Two-out-of-three for equivalences along a `CompStruct`: if the
first edge and the composite are equivalences, so is the second
edge. -/
private theorem isEquivalence_snd_of_compStruct {e₀₁ : Edge x₀ x₁}
    {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) (h₀₁ : e₀₁.IsEquivalence)
    (h₀₂ : e₀₂.IsEquivalence) : e₁₂.IsEquivalence := by
  have : IsIso (HomotopyCategory.homMk e₀₁) := (isEquivalence_iff _).mp h₀₁
  have : IsIso (HomotopyCategory.homMk e₀₁ ≫ HomotopyCategory.homMk e₁₂) := by
    rw [HomotopyCategory.homMk_comp_homMk h]
    exact (isEquivalence_iff _).mp h₀₂
  exact (isEquivalence_iff _).mpr
    (IsIso.of_isIso_comp_left (HomotopyCategory.homMk e₀₁) (HomotopyCategory.homMk e₁₂))

/-- Two-out-of-three for equivalences along a `CompStruct`: if the
second edge and the composite are equivalences, so is the first
edge. -/
private theorem isEquivalence_fst_of_compStruct {e₀₁ : Edge x₀ x₁}
    {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) (h₁₂ : e₁₂.IsEquivalence)
    (h₀₂ : e₀₂.IsEquivalence) : e₀₁.IsEquivalence := by
  have : IsIso (HomotopyCategory.homMk e₁₂) := (isEquivalence_iff _).mp h₁₂
  have : IsIso (HomotopyCategory.homMk e₀₁ ≫ HomotopyCategory.homMk e₁₂) := by
    rw [HomotopyCategory.homMk_comp_homMk h]
    exact (isEquivalence_iff _).mp h₀₂
  exact (isEquivalence_iff _).mpr
    (IsIso.of_isIso_comp_right (HomotopyCategory.homMk e₀₁) (HomotopyCategory.homMk e₁₂))

end Edge

/-- A `2`-simplex whose three face edges are equivalences lies in
the core: every map `⦋1⦌ ⟶ ⦋2⦌` is constant or a face inclusion
`δ i`. -/
private theorem mem_core_obj_two_of_faces {s : X _⦋2⦌}
    (h₀ : (Edge.mk' (X.δ 0 s)).IsEquivalence)
    (h₁ : (Edge.mk' (X.δ 1 s)).IsEquivalence)
    (h₂ : (Edge.mk' (X.δ 2 s)).IsEquivalence) :
    s ∈ (core X).obj (op ⦋2⦌) := by
  intro φ
  have htrich : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by
    intro x
    fin_cases x <;> simp
  have hle : φ.toOrderHom 0 ≤ φ.toOrderHom 1 :=
    φ.toOrderHom.monotone (Fin.zero_le 1)
  rcases htrich (φ.toOrderHom 0) with ha | ha | ha <;>
    rcases htrich (φ.toOrderHom 1) with hb | hb | hb
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 0) ha hb]
    exact isEquivalence_mk'_map_const s 0
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 2) ha hb]
    exact h₂
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 1) ha hb]
    exact h₁
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 1) ha hb]
    exact isEquivalence_mk'_map_const s 1
  · rw [SimplexCategory.Hom.ext_one_left φ (SimplexCategory.δ 0) ha hb]
    exact h₀
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · exfalso
    rw [ha, hb] at hle
    exact absurd hle (by decide)
  · rw [SimplexCategory.Hom.ext_one_left φ
      (SimplexCategory.const ⦋1⦌ ⦋2⦌ 2) ha hb]
    exact isEquivalence_mk'_map_const s 2

/-- The inclusion of the core has the right lifting property
against every horn inclusion in dimension at least `2`, inner or
outer, with no hypothesis on `X`: such a horn contains every
`1`-simplex of `Δ[n + 2]` when `n ≥ 1`
(`SSet.horn_obj_eq_univ`), and in dimension `2` the one missing edge
is recovered from the other two by two-out-of-three along the
`2`-simplex. In other words, a simplex of `X` whose horn
restriction lands in the core already lies in the core. -/
theorem hasLiftingProperty_horn_core_ι {n : ℕ} (i : Fin (n + 3)) :
    HasLiftingProperty Λ[n + 2, i].ι (core X).ι where
  sq_hasLift {f g} sq := by
    have key : ∀ (φ : ⦋1⦌ ⟶ ⦋n + 2⦌),
        stdSimplex.objEquiv.symm φ ∈ Λ[n + 2, i].obj (op ⦋1⦌) →
        (Edge.mk' (X.map φ.op (yonedaEquiv g))).IsEquivalence := by
      intro φ hv
      have hmem :
          (Edge.mk' (f.app (op ⦋1⦌)
            ⟨stdSimplex.objEquiv.symm φ, hv⟩).1).IsEquivalence :=
        mem_core_obj_one_iff.mp (f.app _ ⟨_, hv⟩).2
      have he : (f.app (op ⦋1⦌)
            ⟨stdSimplex.objEquiv.symm φ, hv⟩).1 =
          X.map φ.op (yonedaEquiv g) := by
        have hg : g.app (op ⦋1⦌) (stdSimplex.objEquiv.symm φ) =
            X.map φ.op (yonedaEquiv g) := by
          conv_lhs => rw [← yonedaEquiv.symm_apply_apply g]
          exact yonedaEquiv_symm_app_objEquiv_symm (yonedaEquiv g) φ
        have heq := ConcreteCategory.congr_hom
          (congr_app sq.w (op ⦋1⦌)) ⟨stdSimplex.objEquiv.symm φ, hv⟩
        have he' : (f.app (op ⦋1⦌)
              ⟨stdSimplex.objEquiv.symm φ, hv⟩).1 =
            g.app (op ⦋1⦌) (stdSimplex.objEquiv.symm φ) := by
          simpa using heq
        rw [he', hg]
      rwa [he] at hmem
    have hx : yonedaEquiv g ∈ (core X).obj (op ⦋n + 2⦌) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain ⟨x₀, x₁, x₂, e₀₁, e₁₂, e₀₂, h, hs⟩ :=
          Edge.CompStruct.exists_of_simplex (yonedaEquiv g)
        have e01edge : e₀₁.edge = X.δ 2 (yonedaEquiv g) :=
          h.d₂.symm.trans (by rw [hs])
        have e12edge : e₁₂.edge = X.δ 0 (yonedaEquiv g) :=
          h.d₀.symm.trans (by rw [hs])
        have e02edge : e₀₂.edge = X.δ 1 (yonedaEquiv g) :=
          h.d₁.symm.trans (by rw [hs])
        have face : ∀ (j : Fin 3), j ≠ i →
            (Edge.mk' (X.δ j (yonedaEquiv g))).IsEquivalence :=
          fun j hj ↦ key _ ((objEquiv_symm_δ_mem_horn_iff j i).mpr hj)
        have htrich : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by
          intro x
          fin_cases x <;> simp
        rcases htrich i with rfl | rfl | rfl
        · have hF1 := face 1 (by decide)
          have hF2 := face 2 (by decide)
          have hE01 : e₀₁.IsEquivalence :=
            hF2.of_edge_eq (by simp [e01edge])
          have hE02 : e₀₂.IsEquivalence :=
            hF1.of_edge_eq (by simp [e02edge])
          have hE12 : e₁₂.IsEquivalence :=
            Edge.isEquivalence_snd_of_compStruct h hE01 hE02
          have hF0 : (Edge.mk' (X.δ 0 (yonedaEquiv g))).IsEquivalence :=
            hE12.of_edge_eq (by simp [e12edge])
          exact mem_core_obj_two_of_faces hF0 hF1 hF2
        · have hF0 := face 0 (by decide)
          have hF2 := face 2 (by decide)
          have hE01 : e₀₁.IsEquivalence :=
            hF2.of_edge_eq (by simp [e01edge])
          have hE12 : e₁₂.IsEquivalence :=
            hF0.of_edge_eq (by simp [e12edge])
          have hE02 : e₀₂.IsEquivalence :=
            Edge.IsEquivalence.of_compStruct h hE01 hE12
          have hF1 : (Edge.mk' (X.δ 1 (yonedaEquiv g))).IsEquivalence :=
            hE02.of_edge_eq (by simp [e02edge])
          exact mem_core_obj_two_of_faces hF0 hF1 hF2
        · have hF0 := face 0 (by decide)
          have hF1 := face 1 (by decide)
          have hE12 : e₁₂.IsEquivalence :=
            hF0.of_edge_eq (by simp [e12edge])
          have hE02 : e₀₂.IsEquivalence :=
            hF1.of_edge_eq (by simp [e02edge])
          have hE01 : e₀₁.IsEquivalence :=
            Edge.isEquivalence_fst_of_compStruct h hE12 hE02
          have hF2 : (Edge.mk' (X.δ 2 (yonedaEquiv g))).IsEquivalence :=
            hE01.of_edge_eq (by simp [e01edge])
          exact mem_core_obj_two_of_faces hF0 hF1 hF2
      · intro φ
        refine key φ ?_
        rw [horn_obj_eq_univ i 1 (by omega)]
        exact Set.mem_univ _
    let l : Δ[n + 2] ⟶ (core X : SSet.{u}) :=
      yonedaEquiv.symm ⟨yonedaEquiv g, hx⟩
    have hfac : l ≫ (core X).ι = g := by
      rw [yonedaEquiv_symm_comp]
      simp
    refine CommSq.HasLift.mk' ⟨l, ?_, hfac⟩
    apply (cancel_mono (core X).ι).mp
    rw [Category.assoc, hfac]
    exact sq.w.symm

/-- The inclusion of the core into the ambient simplicial set is
an inner fibration, with no hypothesis on `X`. -/
instance : InnerFibration (core X).ι where
  mem := by
    intro _ _ g hg
    obtain ⟨i, -, -⟩ := hg
    exact hasLiftingProperty_horn_core_ι i

/-- The core of a quasicategory is a quasicategory, because its
inclusion into the ambient simplicial set is an inner fibration. -/
instance [Quasicategory X] : Quasicategory (core X : SSet.{u}) :=
  quasicategory_of_innerFibration (core X).ι

section Nerve

variable {C : Type u} [Category.{v} C]

/-- The `1`-simplex of `nerve C` cut out from an `n`-simplex `F` by
the edge from `a` to `b` is `ComposableArrows.mk₁` of the morphism
`F.obj a ⟶ F.obj b`. -/
private lemma nerve_map_objEquiv_edge {n : ℕ} (F : ComposableArrows C n)
    (a b : Fin (n + 1)) (hab : a ≤ b) :
    (nerve C).map (stdSimplex.objEquiv (stdSimplex.edge.{max u v} n a b hab)).op F =
      ComposableArrows.mk₁ (F.map (homOfLE hab)) :=
  (ComposableArrows.mk₁_hom _).symm

/-- Nerve gate, all-pairs form: an `n`-simplex of `nerve C` lies in
the core if and only if every morphism `F.map' i j` of the
corresponding chain in `C` is an isomorphism. -/
theorem mem_core_nerve_iff_forall_map'_isIso {n : ℕ}
    (F : ComposableArrows C n) :
    F ∈ (core (nerve C)).obj (op ⦋n⦌) ↔
      ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n), IsIso (F.map' i j) := by
  refine (mem_core_obj_iff_forall_edge (X := nerve C) (n := n) (x := F)).trans ?_
  constructor
  · intro h i j hij hjn
    have key := h ⟨i, by omega⟩ ⟨j, by omega⟩ (Fin.mk_le_mk.mpr hij)
    rw [nerve_map_objEquiv_edge] at key
    exact (Edge.isEquivalence_nerve_edgeMk_iff _).mp (key.of_edge_eq rfl)
  · intro h a b hab
    rw [nerve_map_objEquiv_edge]
    exact ((Edge.isEquivalence_nerve_edgeMk_iff _).mpr
      (h a.val b.val (Fin.le_iff_val_le_val.mp hab)
        (Nat.le_of_lt_succ b.isLt))).of_edge_eq rfl

/-- Nerve gate, successive form: an `n`-simplex of `nerve C` lies
in the core if and only if it is a chain of isomorphisms, that is,
every successive morphism `F.map' i (i + 1)` is an isomorphism.
These are the simplices of the nerve of the maximal subgroupoid
`CategoryTheory.Core C`. -/
theorem mem_core_nerve_iff_forall_succ_map'_isIso {n : ℕ}
    (F : ComposableArrows C n) :
    F ∈ (core (nerve C)).obj (op ⦋n⦌) ↔
      ∀ (i : ℕ) (hi : i + 1 ≤ n), IsIso (F.map' i (i + 1)) := by
  refine (mem_core_nerve_iff_forall_map'_isIso F).trans ?_
  constructor
  · intro h i hi
    exact h i (i + 1) (Nat.le_succ i) hi
  · intro h i j hij hjn
    have aux : ∀ (d i : ℕ) (hi : i + d ≤ n),
        IsIso (F.map' i (i + d) (by omega) hi) := by
      intro d
      induction d with
      | zero =>
        intro i _
        change IsIso (F.map' i i (by omega) (by omega))
        rw [F.map'_self i (by omega)]
        infer_instance
      | succ d ih =>
        intro i hi
        have h1 : IsIso (F.map' i (i + d) (by omega) (by omega)) :=
          ih i (by omega)
        have h2 : IsIso (F.map' (i + d) (i + d + 1) (by omega) (by omega)) :=
          h (i + d) hi
        change IsIso (F.map' i (i + d + 1) (by omega) (by omega))
        rw [F.map'_comp i (i + d) (i + d + 1) (by omega) (by omega) (by omega)]
        exact IsIso.comp_isIso' h1 h2
    obtain ⟨d, rfl⟩ := Nat.le.dest hij
    exact aux d i hjn

/-- A `1`-simplex `ComposableArrows.mk₁ f` of `nerve C` lies in
the core if and only if `f` is an isomorphism. -/
theorem mem_core_nerve_mk₁_iff {a b : C} (f : a ⟶ b) :
    ComposableArrows.mk₁ f ∈ (core (nerve C)).obj (op ⦋1⦌) ↔ IsIso f :=
  (mem_core_obj_one_iff (X := nerve C) (s := ComposableArrows.mk₁ f)).trans
    ((Edge.isEquivalence_iff_of_edge_eq (show
        (Edge.mk' (ComposableArrows.mk₁ f)).edge =
          (nerve.edgeMk f).edge from rfl)).trans
      (Edge.isEquivalence_nerve_edgeMk_iff f))

/-- A `2`-simplex `ComposableArrows.mk₂ f g` of `nerve C` lies in
the core if and only if both `f` and `g` are isomorphisms. -/
theorem mem_core_nerve_mk₂_iff {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    ComposableArrows.mk₂ f g ∈ (core (nerve C)).obj (op ⦋2⦌) ↔
      IsIso f ∧ IsIso g := by
  have hf : (ComposableArrows.mk₂ f g).map' 0 1 = f := by dsimp
  have hg : (ComposableArrows.mk₂ f g).map' 1 2 = g := by dsimp
  refine (mem_core_nerve_iff_forall_succ_map'_isIso _).trans ?_
  constructor
  · intro h
    have h1 : IsIso ((ComposableArrows.mk₂ f g).map' 0 1) := h 0 (by omega)
    have h2 : IsIso ((ComposableArrows.mk₂ f g).map' 1 2) := h 1 (by omega)
    rw [hf] at h1
    rw [hg] at h2
    exact ⟨h1, h2⟩
  · intro h i hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    rcases hi01 with rfl | rfl
    · change IsIso ((ComposableArrows.mk₂ f g).map' 0 1)
      rw [hf]
      exact h.1
    · change IsIso ((ComposableArrows.mk₂ f g).map' 1 2)
      rw [hg]
      exact h.2

end Nerve

end SSet

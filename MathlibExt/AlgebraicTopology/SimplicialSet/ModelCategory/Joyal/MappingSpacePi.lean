/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceKanW
public import
  MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv

/-!
# The `π₀` identification for right mapping spaces

Packet T48 of the Joyal model structure programme: this file
closes steps (1) and (2) of TODO(T41-pi-identification) as
recorded in
[MappingSpaceKanW.lean](MappingSpaceKanW.lean) ("What is not
proved here"), and reduces step (3) to the single explicit
hypothesis `hπ` in the assembly theorems of §4. Combined with
packet T42 (`SSet.kanComplex_mappingSpaceRight`) and packet
T41 (`SSet.categoricalEquivalences.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap`
in [MappingSpaceW.lean](MappingSpaceW.lean)), the conclusion
is: a categorical equivalence between quasicategories induces
bijections on `π₀` of all right mapping spaces
(`SSet.categoricalEquivalences.bijective_mapPiZero_mappingSpaceRightMap`),
and is a Dwyer–Kan equivalence as soon as it induces
bijections on the positive based homotopy groups of all right
mapping spaces
(`SSet.categoricalEquivalences.isDwyerKanEquivalence_of_bijective_piMap`).

## The informal proof

Write `H = Hom^R_X(a, b) = SSet.mappingSpaceRight X a b` for
vertex maps `a b : Δ[0] ⟶ X` with underlying vertices
`x = yonedaEquiv a`, `y = yonedaEquiv b`. Transporting along
`SSet.mappingSpaceRight.simplexEquivSucc`, an `n`-simplex of
`H` is an `(n + 1)`-simplex `σ` of `X` whose front face
`frontInclusion n ≫ σ` is constant at `a` and whose last
vertex `rightVertex n ≫ σ` is `b`; faces of `H` correspond to
faces `δ₀, …, δₙ` of `σ`
(`SSet.mappingSpaceRight.simplexEquivSucc_δ`, packet T42).

*§1: the last vertex.* Packet T42 identified
`frontInclusion n = stdSimplex.δ (Fin.last (n + 1))` by a
Day-convolution chase, but left `rightVertex n` as a
transported inclusion. Here `rightVertex n` is pinned down
combinatorially, without redoing the mirror Day chase: like
every map `Δ[0] ⟶ Δ[n + 1]`, it is `stdSimplex.map φ` for a
unique hom `φ : ⦋0⦌ ⟶ ⦋n + 1⦌`, i.e. it is the vertex
inclusion at `k = φ.toOrderHom 0`. The landed face relation
`SSet.rightVertex_comp_δ_castSucc` says
`Fin.succAbove j.castSucc k` is independent of
`j : Fin (n + 2)`. For `j = 0` the value is `k.succ`; if
`k ≠ Fin.last (n + 1)` there is `j` with `j.castSucc = k.succ`,
for which the value is `k.castSucc ≠ k.succ` — a
contradiction. Hence `k` is the last vertex, i.e.
`rightVertex n = stdSimplex.map (inr' ⦋n⦌ ⦋0⦌)`
(`SSet.rightVertex_eq`), and in particular
`rightVertex 0 = stdSimplex.δ 0` (`SSet.rightVertex_zero`).

*§2: `π₀`.* At level `0`, a vertex of `H` is a `1`-simplex of
`X` whose `δ₁`-face is `x` (front condition) and whose
`δ₀`-face is `y` (right-vertex condition, by §1): exactly an
`SSet.Edge x y`
(`SSet.mappingSpaceRight.zeroSimplexEquivEdge`). At level
`1`, a simplex of `H` is a `2`-simplex `Σ` of `X` whose
`δ₂`-face is the degenerate edge at `x`; if `Σ` is an edge of
`H` from `σ` to `τ`, its other faces are the edges for `τ`
(`δ₀`) and `σ` (`δ₁`), so `Σ` is a composite witness
`(Edge.id x)` followed by the `τ`-edge equals the `σ`-edge,
and the two edges represent the same morphism of the ordinary
homotopy category `hX`. This makes
`σ ↦ (zeroSimplexEquivEdge σ).toHoHom` descend to
`π₀ H → (mk x ⟶ mk y)`. It is surjective since morphisms of
`hX` for a quasicategory are represented by single edges
(`SSet.Edge.exists_toHoHom_eq`), and injective since an
equality `(id).toHoHom ≫ e.toHoHom = e'.toHoHom` in `hX` is
witnessed by a `2`-simplex
(`SSet.Edge.nonempty_compStruct_of_toHoHom_comp_eq`), which
transports back to an edge of `H`. This gives
`SSet.mappingSpaceRight.piZeroEquiv :
π₀ (mappingSpaceRight X a b) ≃ (mk x ⟶ mk y)`, natural in
`X` at the level of representing edges
(`SSet.mappingSpaceRight.zeroSimplexEquivEdge_map_app`,
postcomposition, up to the definitional endpoint transport
`yonedaEquiv_comp` recorded by `Edge.ofEq`). Packet T32's
edge-level fullness and faithfulness
(`SSet.dwyerKanFullyFaithfulPiZero`) therefore give
bijectivity of `mapπ₀ (mappingSpaceRight.map X a b f)` for a
categorical equivalence `f` between quasicategories.

*§3–§4: assembly.* With Kan-ness (T42) and the `π₀`
bijection (§2) discharged, the Whitehead criterion
`SSet.KanComplex.W_iff` and packet T41's assembly leave
exactly one input for `KanComplex.W
(mappingSpaceRight.map X a b f)` and for
`isDwyerKanEquivalence f`: bijectivity of
`KanComplex.π.map (mappingSpaceRight.map X a b f) rfl` in
every positive degree at every basepoint. The theorems of §4
are conditional on precisely that hypothesis `hπ`.

## What is not proved here

Step (3) of TODO(T41-pi-identification) remains open: the
identification of the positive homotopy groups
`KanComplex.π (n + 1) (mappingSpaceRight X a b) σ` — defined
through `PtSimplex` homotopy classes, i.e. relative maps
`(Δ[n + 1], ∂Δ[n + 1]) → (H, σ)` with equality detected by
`PtSimplex.RelStruct₀` — with representing edge sets or
hom-sets in probe homotopy categories `h Fun(K, X)`, where
packet T41's `SSet.dwyerKanFullyFaithfulProbes` provides
bijections. The element-level transport used above for `π₀`
does not directly apply: a based `(n + 1)`-simplex of `H`
transports to an `(n + 2)`-simplex of `X` with *all* faces
prescribed (front face constant, remaining faces the
degeneracies of the basepoint edge), homotopies are cylinder
maps out of the non-representable `Δ[n + 1] ⊗ Δ[1]`, and no
landed API identifies these classes with a probe hom-set.
Accordingly `SSet.KanComplex.W
(SSet.mappingSpaceRight.map X a b f)` for a categorical
equivalence is *not* proved unconditionally here; §4 records
the exact remaining hypothesis.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 (mapping spaces).
* *Kerodon*, §4.6 (mapping spaces).
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233v1, §2.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-!
## §1. The transported right vertex is the last vertex

`SSet.rightVertex_eq` and `SSet.rightVertex_zero` now live in
[JoinSlice.lean](../../JoinSlice.lean), next to
`SSet.rightVertex_comp_δ_castSucc` and `SSet.frontInclusion_eq`;
this file consumes them through `MappingSpaceKanW`'s import
chain.
-/

/-!
## §2. Vertices are edges, and `π₀` is the hom-set

Level-wise reading of `SSet.mappingSpaceRight.simplexEquivSucc`
at levels `0` and `1` through §1 and
`SSet.frontInclusion_eq`: vertices are edges, `1`-simplices
are composite witnesses with degenerate front face.
-/

namespace mappingSpaceRight

variable (X : SSet.{u}) (a b : (Δ[0] : SSet.{u}) ⟶ X)

/-- The unique map `Δ[0] ⟶ Δ[0]` is the identity. -/
lemma toDeltaZero_zero_eq_id :
    toDeltaZero (Δ[0] : SSet.{u}) = 𝟙 (Δ[0] : SSet.{u}) :=
  (toDeltaZero_eq _).symm

/-- **Vertices of the right mapping space are edges**: the
`0`-simplices of `mappingSpaceRight X a b` are the edges of
`X` from `yonedaEquiv a` to `yonedaEquiv b`. Via
`SSet.mappingSpaceRight.simplexEquivSucc` at `0`, the front
condition reads `X.δ 1 = yonedaEquiv a` (by
`SSet.frontInclusion_eq`) and the right-vertex condition
reads `X.δ 0 = yonedaEquiv b` (by `SSet.rightVertex_zero`). -/
noncomputable def zeroSimplexEquivEdge :
    (mappingSpaceRight X a b) _⦋0⦌ ≃
      Edge (yonedaEquiv a) (yonedaEquiv b) :=
  (simplexEquivSucc X a b 0).trans
    { toFun := fun σ =>
        Edge.mk (yonedaEquiv σ.1) (by
          have h1 : stdSimplex.δ (Fin.last 1) ≫ σ.1 =
              toDeltaZero (Δ[0] : SSet.{u}) ≫ a := by
            rw [← frontInclusion_eq]
            exact σ.2.1
          have h2 := congrArg yonedaEquiv h1
          have htd : yonedaEquiv (toDeltaZero (Δ[0] : SSet.{u}) ≫ a) =
              yonedaEquiv a := by
            rw [toDeltaZero_zero_eq_id, Category.id_comp]
          rw [stdSimplex.yonedaEquiv_δ_comp, htd] at h2
          exact h2) (by
          have h1 : stdSimplex.δ (0 : Fin 2) ≫ σ.1 = b := by
            rw [← rightVertex_zero]
            exact σ.2.2
          have h2 := congrArg yonedaEquiv h1
          rw [stdSimplex.yonedaEquiv_δ_comp] at h2
          exact h2)
      invFun := fun e =>
        ⟨yonedaEquiv.symm e.edge, by
          have hlast : Fin.last (0 + 1) = (1 : Fin 2) := rfl
          rw [frontInclusion_eq, hlast,
            stdSimplex.δ_comp_yonedaEquiv_symm,
            Edge.src_eq, Equiv.symm_apply_apply, toDeltaZero_zero_eq_id,
            Category.id_comp], by
          rw [rightVertex_zero, stdSimplex.δ_comp_yonedaEquiv_symm,
            Edge.tgt_eq, Equiv.symm_apply_apply]⟩
      left_inv := fun σ => by
        apply Subtype.ext
        change yonedaEquiv.symm (yonedaEquiv σ.1) = σ.1
        rw [Equiv.symm_apply_apply]
      right_inv := fun e => by
        apply Edge.ext
        change yonedaEquiv (yonedaEquiv.symm e.edge) = e.edge
        rw [Equiv.apply_symm_apply] }

/-- The underlying `1`-simplex of the edge associated to a
vertex of the right mapping space is the transported
`1`-simplex of `X`. -/
@[simp]
lemma zeroSimplexEquivEdge_edge (σ : (mappingSpaceRight X a b) _⦋0⦌) :
    (zeroSimplexEquivEdge X a b σ).edge =
      yonedaEquiv ((simplexEquivSucc X a b 0 σ).1) :=
  rfl

/-- The transported `1`-simplex of the vertex associated to
an edge is the edge's own classifying map. -/
lemma simplexEquivSucc_zero_zeroSimplexEquivEdge_symm
    (e : Edge (yonedaEquiv a) (yonedaEquiv b)) :
    ((simplexEquivSucc X a b 0) ((zeroSimplexEquivEdge X a b).symm e)).1 =
      yonedaEquiv.symm e.edge := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← zeroSimplexEquivEdge_edge,
    Equiv.apply_symm_apply]

/-- The constant `1`-simplex at `a'`, as a simplex of `X`,
is the degeneracy of the vertex. -/
lemma yonedaEquiv_toDeltaZero_one_comp (a' : (Δ[0] : SSet.{u}) ⟶ X) :
    yonedaEquiv (toDeltaZero (Δ[1] : SSet.{u}) ≫ a') =
      X.σ 0 (yonedaEquiv a') := by
  have htd : toDeltaZero (Δ[1] : SSet.{u}) =
      stdSimplex.σ (0 : Fin 1) := (toDeltaZero_eq _).symm
  rw [htd, stdSimplex.yonedaEquiv_σ_comp]

/-- The `δ₂`-face of the transported `2`-simplex of a
`1`-simplex of the mapping space is the degenerate edge at
the source vertex (the front-face condition). -/
lemma δ_two_yonedaEquiv_simplexEquivSucc_one
    (η : (mappingSpaceRight X a b) _⦋1⦌) :
    X.δ 2 (yonedaEquiv ((simplexEquivSucc X a b 1 η).1)) =
      X.σ 0 (yonedaEquiv a) := by
  have h1 : stdSimplex.δ (Fin.last 2) ≫ (simplexEquivSucc X a b 1 η).1 =
      toDeltaZero (Δ[1] : SSet.{u}) ≫ a := by
    rw [← frontInclusion_eq]
    exact (simplexEquivSucc X a b 1 η).2.1
  have h2 := congrArg yonedaEquiv h1
  rw [stdSimplex.yonedaEquiv_δ_comp,
    yonedaEquiv_toDeltaZero_one_comp] at h2
  exact h2

/-- The `δ₀`-face of the transported `2`-simplex of a
`1`-simplex of the mapping space is the edge of its
`δ₀`-face in the mapping space. -/
lemma δ_zero_yonedaEquiv_simplexEquivSucc_one
    (η : (mappingSpaceRight X a b) _⦋1⦌) :
    X.δ 0 (yonedaEquiv ((simplexEquivSucc X a b 1 η).1)) =
      (zeroSimplexEquivEdge X a b ((mappingSpaceRight X a b).δ 0 η)).edge := by
  rw [zeroSimplexEquivEdge_edge, ← stdSimplex.yonedaEquiv_δ_comp]
  congr 1
  exact (simplexEquivSucc_δ a b η 0).symm

/-- The `δ₁`-face of the transported `2`-simplex of a
`1`-simplex of the mapping space is the edge of its
`δ₁`-face in the mapping space. -/
lemma δ_one_yonedaEquiv_simplexEquivSucc_one
    (η : (mappingSpaceRight X a b) _⦋1⦌) :
    X.δ 1 (yonedaEquiv ((simplexEquivSucc X a b 1 η).1)) =
      (zeroSimplexEquivEdge X a b ((mappingSpaceRight X a b).δ 1 η)).edge := by
  rw [zeroSimplexEquivEdge_edge, ← stdSimplex.yonedaEquiv_δ_comp]
  congr 1
  exact (simplexEquivSucc_δ a b η 1).symm

/-- An edge of the mapping space transports to a composite
witness in `X` with degenerate first edge, so its endpoints
represent the same morphism of `hX`. -/
lemma toHoHom_zeroSimplexEquivEdge_eq_of_edge
    {σ τ : (mappingSpaceRight X a b) _⦋0⦌}
    (e : (mappingSpaceRight X a b).Edge σ τ) :
    (zeroSimplexEquivEdge X a b σ).toHoHom =
      (zeroSimplexEquivEdge X a b τ).toHoHom := by
  have hσ : (mappingSpaceRight X a b).δ 1 e.edge = σ := Edge.src_eq e
  have hτ : (mappingSpaceRight X a b).δ 0 e.edge = τ := Edge.tgt_eq e
  have c : Edge.CompStruct (Edge.id (yonedaEquiv a))
      (zeroSimplexEquivEdge X a b τ) (zeroSimplexEquivEdge X a b σ) :=
    Edge.CompStruct.mk
      (yonedaEquiv ((simplexEquivSucc X a b 1 e.edge).1))
      (by rw [Edge.id_edge]; exact δ_two_yonedaEquiv_simplexEquivSucc_one X a b e.edge)
      (by rw [δ_zero_yonedaEquiv_simplexEquivSucc_one X a b e.edge, hτ])
      (by rw [δ_one_yonedaEquiv_simplexEquivSucc_one X a b e.edge, hσ])
  have h := Edge.toHoHom_comp c
  rw [Edge.toHoHom_id, Category.id_comp] at h
  exact h.symm

/-- `inr' ⦋1⦌ ⦋0⦌` is `δ₀ ≫ δ₀`: the last vertex of
`Δ[2]` is the `δ₀`-face of the `δ₀`-face. -/
lemma inr'_one_zero :
    AugmentedSimplexCategory.inr' ⦋1⦌ ⦋0⦌ =
      SimplexCategory.δ (0 : Fin 2) ≫ SimplexCategory.δ (0 : Fin 3) := by
  ext i : 3
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply]
  rw [inr'_toOrderHom_zero]
  simp [SimplexCategory.δ]

/-- Conversely, an equality of represented morphisms in
`hX` is witnessed by a `2`-simplex of `X`
(`SSet.Edge.nonempty_compStruct_of_toHoHom_comp_eq`), which
transports to an edge of the mapping space: the vertices
lie in the same connected component. -/
lemma π₀_mk_eq_of_toHoHom_zeroSimplexEquivEdge_eq [Quasicategory X]
    {σ τ : (mappingSpaceRight X a b) _⦋0⦌}
    (h : (zeroSimplexEquivEdge X a b σ).toHoHom =
      (zeroSimplexEquivEdge X a b τ).toHoHom) :
    π₀.mk σ = π₀.mk τ := by
  have hcomp : (Edge.id (yonedaEquiv a)).toHoHom ≫
        (zeroSimplexEquivEdge X a b σ).toHoHom =
      (zeroSimplexEquivEdge X a b τ).toHoHom := by
    rw [Edge.toHoHom_id, Category.id_comp]
    exact h
  obtain ⟨c⟩ := Edge.nonempty_compStruct_of_toHoHom_comp_eq hcomp
  have hd2 : X.δ 2 c.simplex = X.σ 0 (yonedaEquiv a) := by
    have h2 := c.d₂
    rwa [Edge.id_edge] at h2
  have hd0 : X.δ 0 c.simplex = (zeroSimplexEquivEdge X a b σ).edge := c.d₀
  have hd1 : X.δ 1 c.simplex = (zeroSimplexEquivEdge X a b τ).edge := c.d₁
  have hfront : frontInclusion 1 ≫ yonedaEquiv.symm c.simplex =
      toDeltaZero (Δ[1] : SSet.{u}) ≫ a := by
    apply yonedaEquiv.injective
    have h2 : frontInclusion 1 ≫ yonedaEquiv.symm c.simplex =
        stdSimplex.δ (Fin.last 2) ≫ yonedaEquiv.symm c.simplex := by
      rw [frontInclusion_eq]
    rw [h2, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change X.δ (2 : Fin 3) c.simplex =
      yonedaEquiv (toDeltaZero (Δ[1] : SSet.{u}) ≫ a)
    rw [hd2, yonedaEquiv_toDeltaZero_one_comp]
  have hright : rightVertex 1 ≫ yonedaEquiv.symm c.simplex = b := by
    apply yonedaEquiv.injective
    rw [rightVertex_eq, ← yonedaEquiv_naturality, Equiv.apply_symm_apply,
      inr'_one_zero, op_comp, Functor.map_comp]
    change X.δ 0 (X.δ 0 c.simplex) = yonedaEquiv b
    rw [hd0]
    exact Edge.tgt_eq _
  set η := (simplexEquivSucc X a b 1).symm
    ⟨yonedaEquiv.symm c.simplex, hfront, hright⟩ with hηdef
  have hη1 : ((simplexEquivSucc X a b 1) η).1 =
      yonedaEquiv.symm c.simplex := by
    rw [hηdef]
    exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hδ0 : (mappingSpaceRight X a b).δ 0 η = σ := by
    apply (zeroSimplexEquivEdge X a b).injective
    apply Edge.ext
    have hh := δ_zero_yonedaEquiv_simplexEquivSucc_one X a b η
    rw [hη1, Equiv.apply_symm_apply] at hh
    exact hh.symm.trans hd0
  have hδ1 : (mappingSpaceRight X a b).δ 1 η = τ := by
    apply (zeroSimplexEquivEdge X a b).injective
    apply Edge.ext
    have hh := δ_one_yonedaEquiv_simplexEquivSucc_one X a b η
    rw [hη1, Equiv.apply_symm_apply] at hh
    exact hh.symm.trans hd1
  exact (π₀.sound (Edge.mk η hδ1 hδ0)).symm

/-- **`π₀` of the right mapping space is the hom-set**:
for a quasicategory `X`, the connected components of
`mappingSpaceRight X a b` are the morphisms
`mk (yonedaEquiv a) ⟶ mk (yonedaEquiv b)` of the ordinary
homotopy category, via the represented edge. This is step
(2) of TODO(T41-pi-identification) in
[MappingSpaceKanW.lean](MappingSpaceKanW.lean). -/
noncomputable def piZeroEquiv [Quasicategory X] :
    π₀ (mappingSpaceRight X a b) ≃
      (HomotopyCategory.mk (yonedaEquiv a) ⟶
        HomotopyCategory.mk (yonedaEquiv b)) :=
  Equiv.ofBijective
    (π₀.lift (fun σ => (zeroSimplexEquivEdge X a b σ).toHoHom)
      (fun {σ τ} e => toHoHom_zeroSimplexEquivEdge_eq_of_edge X a b e))
    ⟨by
      intro c₁ c₂ h
      obtain ⟨σ, rfl⟩ := π₀.mk_surjective c₁
      obtain ⟨τ, rfl⟩ := π₀.mk_surjective c₂
      simp only [π₀.lift_mk] at h
      exact π₀_mk_eq_of_toHoHom_zeroSimplexEquivEdge_eq X a b h,
    by
      intro ξ
      obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq ξ
      exact ⟨π₀.mk ((zeroSimplexEquivEdge X a b).symm e), by
        simp only [π₀.lift_mk, Equiv.apply_symm_apply]
        exact he⟩⟩

/-- The component of a vertex maps to the morphism
represented by its edge. -/
@[simp]
lemma piZeroEquiv_mk [Quasicategory X]
    (σ : (mappingSpaceRight X a b) _⦋0⦌) :
    piZeroEquiv X a b (π₀.mk σ) =
      (zeroSimplexEquivEdge X a b σ).toHoHom :=
  rfl

variable {Y : SSet.{u}}

/-- **Naturality of the vertex–edge identification**: the
edge of the image of a vertex under
`SSet.mappingSpaceRight.map` is the postcomposition of its
edge, transported along the endpoint identification
`SSet.yonedaEquiv_comp`. -/
lemma zeroSimplexEquivEdge_map_app (f : X ⟶ Y)
    (σ : (mappingSpaceRight X a b) _⦋0⦌) :
    zeroSimplexEquivEdge Y (a ≫ f) (b ≫ f) ((map X a b f).app _ σ) =
      ((zeroSimplexEquivEdge X a b σ).map f).ofEq
        (yonedaEquiv_comp a f).symm (yonedaEquiv_comp b f).symm := by
  apply Edge.ext
  have hL : (zeroSimplexEquivEdge Y (a ≫ f) (b ≫ f)
        ((map X a b f).app _ σ)).edge =
      f.app _ (yonedaEquiv ((simplexEquivSucc X a b 0 σ).1)) := by
    rw [zeroSimplexEquivEdge_edge, ← yonedaEquiv_comp,
      simplexEquivSucc_map_app_val]
  have hR : (((zeroSimplexEquivEdge X a b σ).map f).ofEq
        (yonedaEquiv_comp a f).symm (yonedaEquiv_comp b f).symm).edge =
      f.app _ (yonedaEquiv ((simplexEquivSucc X a b 0 σ).1)) := by
    change f.app _ ((zeroSimplexEquivEdge X a b σ).edge) =
      f.app _ (yonedaEquiv ((simplexEquivSucc X a b 0 σ).1))
    rw [zeroSimplexEquivEdge_edge]
  exact hL.trans hR.symm

end mappingSpaceRight

variable {X Y : SSet.{u}} {f : X ⟶ Y}

/-!
## §3. Categorical equivalences are bijective on `π₀`

Transport of represented morphisms along vertex equalities,
then packet T32's edge-level fullness and faithfulness read
through `SSet.mappingSpaceRight.piZeroEquiv`.
-/

/-- The represented morphism of an edge transported along
endpoint equalities is the conjugate by the corresponding
`eqToHom` maps. -/
lemma Edge.toHoHom_ofEq {Z : SSet.{u}} {x₀ x₁ y₀ y₁ : Z _⦋0⦌}
    (e : Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    (e.ofEq h₀ h₁).toHoHom =
      eqToHom (congrArg HomotopyCategory.mk h₀).symm ≫ e.toHoHom ≫
        eqToHom (congrArg HomotopyCategory.mk h₁) := by
  simp only [Edge.toHoHom_eq_homMk]
  cases h₀
  cases h₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1

/-- Equality of represented morphisms can be moved across
an endpoint transport, at the cost of transporting the other
side inversely. -/
lemma Edge.toHoHom_ofEq_eq_iff {Z : SSet.{u}}
    {x₀ x₁ y₀ y₁ : Z _⦋0⦌} (e : Edge x₀ x₁) (e' : Edge y₀ y₁)
    (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    (e.ofEq h₀ h₁).toHoHom = e'.toHoHom ↔
      e.toHoHom = (e'.ofEq h₀.symm h₁.symm).toHoHom := by
  cases h₀
  cases h₁
  simp only [Edge.toHoHom_ofEq, eqToHom_refl, Category.id_comp,
    Category.comp_id]

/-- **A categorical equivalence between quasicategories is
bijective on `π₀` of right mapping spaces**: this is the
`h₀` input of packet T41's
`SSet.dwyerKanFullyFaithful.of_kan_bijective_mapPiZero_piMap`,
from the `π₀` identification
`SSet.mappingSpaceRight.piZeroEquiv` and packet T32's
`SSet.categoricalEquivalences.dwyerKanFullyFaithfulPiZero`
(edge forms). -/
theorem categoricalEquivalences.bijective_mapPiZero_mappingSpaceRightMap
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f)
    (a b : (Δ[0] : SSet.{u}) ⟶ X) :
    Function.Bijective (mapπ₀ (mappingSpaceRight.map X a b f)) := by
  have hf0 : SSet.dwyerKanFullyFaithfulPiZero f :=
    categoricalEquivalences.dwyerKanFullyFaithfulPiZero hf
  refine ⟨?_, ?_⟩
  · intro c₁ c₂ h
    obtain ⟨σ, rfl⟩ := π₀.mk_surjective c₁
    obtain ⟨τ, rfl⟩ := π₀.mk_surjective c₂
    rw [mapπ₀_mk, mapπ₀_mk] at h
    apply (mappingSpaceRight.piZeroEquiv X a b).injective
    rw [mappingSpaceRight.piZeroEquiv_mk, mappingSpaceRight.piZeroEquiv_mk]
    apply hf0.edge_map_toHoHom_injective (x := yonedaEquiv a)
      (y := yonedaEquiv b)
    have h2 := congrArg (mappingSpaceRight.piZeroEquiv Y (a ≫ f) (b ≫ f)) h
    rw [mappingSpaceRight.piZeroEquiv_mk, mappingSpaceRight.piZeroEquiv_mk,
      mappingSpaceRight.zeroSimplexEquivEdge_map_app,
      mappingSpaceRight.zeroSimplexEquivEdge_map_app,
      Edge.toHoHom_ofEq, Edge.toHoHom_ofEq] at h2
    exact (cancel_mono _).mp ((cancel_epi _).mp h2)
  · intro c'
    obtain ⟨τ', rfl⟩ := π₀.mk_surjective c'
    obtain ⟨e, he⟩ := hf0.exists_edge_map_toHoHom_eq (x := yonedaEquiv a)
      (y := yonedaEquiv b)
      ((mappingSpaceRight.zeroSimplexEquivEdge Y (a ≫ f) (b ≫ f) τ').ofEq
        (yonedaEquiv_comp a f) (yonedaEquiv_comp b f))
    refine ⟨π₀.mk ((mappingSpaceRight.zeroSimplexEquivEdge X a b).symm e), ?_⟩
    rw [mapπ₀_mk]
    apply (mappingSpaceRight.piZeroEquiv Y (a ≫ f) (b ≫ f)).injective
    rw [mappingSpaceRight.piZeroEquiv_mk, mappingSpaceRight.piZeroEquiv_mk,
      mappingSpaceRight.zeroSimplexEquivEdge_map_app,
      Equiv.apply_symm_apply]
    rw [Edge.toHoHom_ofEq_eq_iff]
    have hedge :
        ((mappingSpaceRight.zeroSimplexEquivEdge Y (a ≫ f) (b ≫ f) τ').ofEq
            (yonedaEquiv_comp a f).symm.symm
              (yonedaEquiv_comp b f).symm.symm) =
          ((mappingSpaceRight.zeroSimplexEquivEdge Y (a ≫ f) (b ≫ f) τ').ofEq
            (yonedaEquiv_comp a f) (yonedaEquiv_comp b f)) := by
      apply Edge.ext
      rfl
    rw [hedge]
    exact he

/-!
## §4. The Whitehead assembly, conditional on positive `π`

The remaining input of TODO(T41-pi-identification) step (3),
isolated as hypothesis `hπ`: see "What is not proved here"
in the header.
-/

/-- **Pointwise Whitehead conclusion**: for a categorical
equivalence between quasicategories, the induced map on a
right mapping space is a `SSet.KanComplex.W` weak
equivalence as soon as it is bijective on all positive based
homotopy groups (hypothesis `hπ`). Kan-ness is packet T42
(global instance), the `π₀` bijection is §3, and the
criterion is `SSet.KanComplex.W_iff`. -/
theorem categoricalEquivalences.kanComplexW_mappingSpaceRightMap_of_bijective_piMap
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f)
    (a b : (Δ[0] : SSet.{u}) ⟶ X)
    (hπ : ∀ (n : ℕ) (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    KanComplex.W (mappingSpaceRight.map X a b f) :=
  (KanComplex.W_iff _).2
    ⟨categoricalEquivalences.bijective_mapPiZero_mappingSpaceRightMap hf a b,
      hπ⟩

/-- **A categorical equivalence between quasicategories is
a Dwyer–Kan equivalence, conditional on positive `π`**: this
is packet T41's
`SSet.categoricalEquivalences.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap`
with its Kan hypotheses discharged by packet T42 and its
`π₀` hypothesis discharged by §3, leaving exactly the
positive-homotopy-group hypothesis `hπ` (step (3) of
TODO(T41-pi-identification)). -/
theorem categoricalEquivalences.isDwyerKanEquivalence_of_bijective_piMap
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f)
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    isDwyerKanEquivalence f :=
  categoricalEquivalences.isDwyerKanEquivalence_of_kan_bijective_mapPiZero_piMap
    hf
    (fun a b => kanComplex_mappingSpaceRight X a b)
    (fun a b => kanComplex_mappingSpaceRight Y (a ≫ f) (b ≫ f))
    (fun a b =>
      categoricalEquivalences.bijective_mapPiZero_mappingSpaceRightMap hf a b)
    hπ

/-- The fully-faithful half of
`SSet.categoricalEquivalences.isDwyerKanEquivalence_of_bijective_piMap`:
a categorical equivalence between quasicategories satisfying
`hπ` induces `SSet.KanComplex.W` weak equivalences on all
right mapping spaces. -/
theorem categoricalEquivalences.dwyerKanFullyFaithful_of_bijective_piMap
    [Quasicategory X] [Quasicategory Y] (hf : categoricalEquivalences f)
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n + 1) (x := σ))) :
    dwyerKanFullyFaithful f :=
  isDwyerKanEquivalence.dwyerKanFullyFaithful
    (categoricalEquivalences.isDwyerKanEquivalence_of_bijective_piMap hf hπ)

end SSet

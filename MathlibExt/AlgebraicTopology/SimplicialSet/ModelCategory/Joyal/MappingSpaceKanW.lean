/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinProperties
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlice
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceW
public import
  MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral

/-!
# Right mapping spaces of a quasicategory are Kan complexes

Write `H = Hom^R_X(x, y) = SSet.mappingSpaceRight X x y`. An
`n`-simplex of `H` is a map `Δ[n] ⋆ Δ[0] ⟶ X` whose left
restriction is constant at `x` and whose right restriction is `y`;
transporting along `SSet.joinStdSimplexIso n 0 : Δ[n] ⋆ Δ[0] ≅
Δ[n + 1]` (`SSet.mappingSpaceRight.simplexEquivSucc`), it is an
`(n + 1)`-simplex `σ : Δ[n + 1] ⟶ X` whose front face
`δ_{n+1} σ` (vertices `0, …, n`) is the constant `n`-simplex at
`x` and whose last vertex (vertex `n + 1`) is `y`. The face maps
of `H` correspond, under this transport, to the face maps
`δ₀, …, δₙ` of `σ`: the simplicial operators on `H` are joins of
operators on the left factor, and joining with `Δ[0]` appends one
last vertex.

Now let `Λ[n + 1, i] ⟶ H` be a horn, given as a compatible family
of `n`-simplices `f_j` of `H` for `j ≠ i`. Transporting, we get
`(n + 1)`-simplices `s_j` of `X` for `j = 0, …, n + 1`, `j ≠ i`,
each with constant front face at `x` and last vertex `y`, and
pairwise compatible on common faces `δ_a s_j = δ_{j-1} s_a`.
Adjoin one more face: the constant `(n + 1)`-simplex at `x` as
face `n + 2`. It is compatible with every `s_j`: one side of the
compatibility is the constant `n`-simplex at `x` because the
extra face is constant, and the other side is the front face of
`s_j`, which is constant at `x` by the mapping-space condition.
We have built a horn `Λ[n + 2, i] ⟶ X` (with `i` read in
`Fin (n + 3)` via `Fin.castSucc`).
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-!
## §1. Right mapping spaces of a quasicategory are Kan

The horn transport described in the header: faces of the join
model correspond to faces `δ₀, …, δₙ` of the transported simplex
(`SSet.mappingSpaceRight.simplexEquivSucc_δ`), so a horn in the
mapping space plus the constant front face is a horn in `X`,
inner unless it is the left outer horn, in which case it is
special with degenerate critical edge.
-/

namespace mappingSpaceRight

/-- The `1`-simplex of `Δ[n + 2]` spanning vertices `0` and `1`
factors through the front face: `δ (last) ∘ (edge (0,1) of
Δ[n + 1]) = edge (0,1) of Δ[n + 2]`, as simplex-category homs. -/
lemma edge01_comp_δ_last (n : ℕ) :
    (stdSimplex.edge.{u} (n + 1) 0 ⟨1, by omega⟩ (by simp)).down ≫
        SimplexCategory.δ (Fin.last (n + 2)) =
      (stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩ (by simp)).down := by
  ext a : 3
  fin_cases a <;>
    simp [SimplexCategory.δ,
      stdSimplex.coe_edge_down_toOrderHom]

/-- **Face transport**: the `a`-th face of a simplex of the
right mapping space corresponds, under
`mappingSpaceRight.simplexEquivSucc`, to the `a.castSucc`-th
face of the transported simplex of `X`. From
`SSet.mappingSpaceRight.map_val`,
`SSet.joinStdSimplexIso_inv_comp_join_map_app` and
`SSet.tensorHomOf_δ_id`. -/
theorem simplexEquivSucc_δ {X : SSet.{u}} (x y : (Δ[0] : SSet.{u}) ⟶ X)
    {k : ℕ} (σ : (mappingSpaceRight X x y).obj (op ⦋k + 1⦌))
    (a : Fin (k + 2)) :
    ((simplexEquivSucc X x y k) ((mappingSpaceRight X x y).δ a σ)).1 =
      stdSimplex.δ a.castSucc ≫
        ((simplexEquivSucc X x y (k + 1)) σ).1 := by
  have hval : ∀ (t : ℕ) (τ : (mappingSpaceRight X x y).obj (op ⦋t⦌)),
      ((simplexEquivSucc X x y t) τ).1 =
        (joinStdSimplexIso.{u} t 0).inv ≫ τ.1 := fun t τ ↦ rfl
  rw [hval k, hval (k + 1)]
  have hδ : ((mappingSpaceRight X x y).δ a σ).1 =
      (join.{u}.map (SSet.stdSimplex.map (SimplexCategory.δ a))).app
          (Δ[0] : SSet.{u}) ≫ σ.1 := rfl
  rw [hδ, ← Category.assoc (joinStdSimplexIso.{u} k 0).inv,
    joinStdSimplexIso_inv_comp_join_map_app, tensorHomOf_δ_id,
    ← stdSimplex_δ_eq_map,
    Category.assoc (stdSimplex.δ a.castSucc)]

end mappingSpaceRight

/-- **Right mapping spaces of a quasicategory are Kan
complexes** (the additional comparison obligation of `MappingSpaceW.lean`). The proof
is the horn transport of the header: one-dimensional horns are
filled by degeneracies; in higher dimensions a horn
`Λ[n + 1, i]` in `Hom^R_X(x, y)` together with the constant
front face is a horn `Λ[n + 2, i.castSucc]` in `X`, which is
inner for `i ≠ 0` (filled since `X` is a quasicategory) and a
special left outer horn for `i = 0`, whose critical `(0, 1)`
edge lies in the constant front face, hence is the degenerate
identity edge at `x`, an equivalence (filled by
`SSet.hasSpecialOuterHornFilling_of_quasicategory`). -/
theorem kanComplex_mappingSpaceRight (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceRight X x y) := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain _ | n := n
  · -- One-dimensional horns: fill by the degenerate edge.
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin 2, j ≠ i := by
      by_cases hi : i = 0
      · exact ⟨1, by simp [hi]⟩
      · exact ⟨0, Ne.symm hi⟩
    have hδσ : stdSimplex.δ j₀ ≫ stdSimplex.σ (0 : Fin 1) =
        𝟙 (Δ[0] : SSet.{u}) := by
      have hσ : (stdSimplex.σ (0 : Fin 1) :
            (Δ[1] : SSet.{u}) ⟶ Δ[0]) =
          SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) := rfl
      rw [stdSimplex_δ_eq_map, hσ, ← CategoryTheory.Functor.map_comp]
      have hcomp : SimplexCategory.δ j₀ ≫
          SimplexCategory.σ (0 : Fin 1) = 𝟙 ⦋0⦌ := by
        fin_cases j₀
        · exact SimplexCategory.δ_comp_σ_self
        · exact SimplexCategory.δ_comp_σ_succ
      rw [hcomp, CategoryTheory.Functor.map_id]
    refine ⟨stdSimplex.σ 0 ≫ f j₀ hj₀, fun j hj ↦ ?_⟩
    have hji : j = j₀ := by
      have h1 : j.val < 2 := j.is_lt
      have h2 : j₀.val < 2 := j₀.is_lt
      have h3 : i.val < 2 := i.is_lt
      apply Fin.ext
      simp only [ne_eq, Fin.ext_iff] at hj hj₀
      omega
    subst hji
    rw [← Category.assoc, hδσ, Category.id_comp]
  · -- Higher-dimensional horns: transport to `X`.
    -- The transported faces `s j : Δ[n + 2] ⟶ X`.
    set s : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 2] : SSet.{u}) ⟶ X :=
      fun j hj ↦
        ((mappingSpaceRight.simplexEquivSucc X x y (n + 1))
          (yonedaEquiv (f j hj))).1 with hs
    have hsfront : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        stdSimplex.δ (Fin.last (n + 2)) ≫ s j hj =
          toDeltaZero (Δ[n + 1] : SSet.{u}) ≫ x := by
      intro j hj
      have hcond :=
        ((mappingSpaceRight.simplexEquivSucc X x y (n + 1))
          (yonedaEquiv (f j hj))).2.1
      calc stdSimplex.δ (Fin.last (n + 2)) ≫ s j hj
          = frontInclusion (n + 1) ≫
              ((mappingSpaceRight.simplexEquivSucc X x y (n + 1))
                (yonedaEquiv (f j hj))).1 := by
            simp only [hs, frontInclusion_eq]
        _ = toDeltaZero (Δ[n + 1] : SSet.{u}) ≫ x := hcond
    have hsright : ∀ (j : Fin (n + 3)) (hj : j ≠ i),
        rightVertex (n + 1) ≫ s j hj = y :=
      fun j hj ↦
        ((mappingSpaceRight.simplexEquivSucc X x y (n + 1))
          (yonedaEquiv (f j hj))).2.2
    -- The horn in `X`: add the constant front face.
    set g : ∀ (k : Fin (n + 4)) (_ : k ≠ i.castSucc),
        (Δ[n + 2] : SSet.{u}) ⟶ X := fun k hk ↦
      if hlast : k = Fin.last (n + 3) then toDeltaZero Δ[n + 2] ≫ x
      else s (k.castPred hlast)
        (fun h ↦ hk (by rw [← Fin.castSucc_castPred k hlast, h])) with hg
    have hg_castSucc : ∀ (j : Fin (n + 3)) (hj : j ≠ i)
        (h : j.castSucc ≠ i.castSucc), g j.castSucc h = s j hj := by
      intro j hj h
      exact dite_eq_right (Fin.ne_last_of_lt (Fin.castSucc_lt_last j))
    have hg_last : ∀ (h : Fin.last (n + 3) ≠ i.castSucc),
        g (Fin.last (n + 3)) h = toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ x := by
      intro h
      exact dite_eq_left rfl
    have hcompat : horn.IsCompatible g := by
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      by_cases hk_last : k = Fin.last (n + 3)
      · -- Compatibility with the constant front face.
        subst hk_last
        obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
        have hj' : j' ≠ i := fun h ↦ hj (by rw [h])
        have hgl : g (Fin.last (n + 3)) hk =
            toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ x := hg_last hk
        have hgj : g j'.castSucc hj = s j' hj' :=
          hg_castSucc j' hj' hj
        have htd : stdSimplex.δ j' ≫ toDeltaZero (Δ[n + 2] : SSet.{u}) =
            toDeltaZero (Δ[n + 1] : SSet.{u}) := toDeltaZero_eq _
        rw [hgj, hgl, Fin.pred_last, Fin.castPred_castSucc,
          hsfront j' hj', ← Category.assoc (stdSimplex.δ j'), htd]
      · -- Compatibility of two transported faces: reduce to `hf`.
        obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
        obtain ⟨k', rfl⟩ := k.eq_castSucc_of_ne_last hk_last
        have hj' : j' ≠ i := fun h ↦ hj (by rw [h])
        have hk' : k' ≠ i := fun h ↦ hk (by rw [h])
        have hjk' : j' < k' := Fin.castSucc_lt_castSucc_iff.mp hjk
        have hgj : g j'.castSucc hj = s j' hj' :=
          hg_castSucc j' hj' hj
        have hgk : g k'.castSucc hk = s k' hk' :=
          hg_castSucc k' hk' hk
        have hδδ : ∀ (a : Fin (n + 2)) (φ : (Δ[n + 1] : SSet.{u}) ⟶
              mappingSpaceRight X x y),
            (mappingSpaceRight X x y).δ a (yonedaEquiv φ) =
              yonedaEquiv (stdSimplex.δ a ≫ φ) := by
          intro a φ
          have h := stdSimplex.δ_comp_yonedaEquiv_symm
            (X := mappingSpaceRight X x y) (i := a) (x := yonedaEquiv φ)
          rw [Equiv.symm_apply_apply] at h
          calc (mappingSpaceRight X x y).δ a (yonedaEquiv φ)
              = yonedaEquiv (yonedaEquiv.symm
                  ((mappingSpaceRight X x y).δ a (yonedaEquiv φ))) :=
                (Equiv.apply_symm_apply _ _).symm
            _ = yonedaEquiv (stdSimplex.δ a ≫ φ) := by rw [← h]
        have hidx : (j'.castSucc).castPred (Fin.ne_last_of_lt hjk) =
            Fin.castSucc (j'.castPred (Fin.ne_last_of_lt hjk')) := by
          ext
          simp only [Fin.coe_castPred, Fin.val_castSucc]
        have hRHS : stdSimplex.δ
              (Fin.castSucc (j'.castPred (Fin.ne_last_of_lt hjk'))) ≫
              s k' hk' =
            ((mappingSpaceRight.simplexEquivSucc X x y n)
              (yonedaEquiv (stdSimplex.δ
                (j'.castPred (Fin.ne_last_of_lt hjk')) ≫
                  f k' hk'))).1 := by
          rw [show s k' hk' =
              ((mappingSpaceRight.simplexEquivSucc X x y (n + 1))
                (yonedaEquiv (f k' hk'))).1 from rfl,
            ← mappingSpaceRight.simplexEquivSucc_δ x y
              (yonedaEquiv (f k' hk'))
              (j'.castPred (Fin.ne_last_of_lt hjk')), hδδ]
        rw [hgj, hgk, ← Fin.castSucc_pred_eq_pred_castSucc
          (Fin.ne_zero_of_lt hjk'),
          ← mappingSpaceRight.simplexEquivSucc_δ x y
            (yonedaEquiv (f j' hj')) (k'.pred (Fin.ne_zero_of_lt hjk')),
          hδδ, hidx, hRHS]
        exact congrArg (fun τ =>
          ((mappingSpaceRight.simplexEquivSucc X x y n) τ).1)
          (congrArg yonedaEquiv (hf.δ_pred_comp j' k' hj' hk' hjk'))
    -- Fill the horn in `X`.
    obtain ⟨Φ, hΦ⟩ : ∃ (Φ : (Δ[n + 3] : SSet.{u}) ⟶ X),
        ∀ (k : Fin (n + 4)) (hk : k ≠ i.castSucc),
          stdSimplex.δ k ≫ Φ = g k hk := by
      by_cases hi : i = 0
      · subst hi
        obtain ⟨σ₀, hσ₀⟩ := hcompat.exists_desc
        have hedge : (leftHornEdge.{u} σ₀).IsEquivalence := by
          have hed : (leftHornEdge.{u} σ₀).edge =
              X.σ 0 (yonedaEquiv x) := by
            change σ₀.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} (n + 1)) =
              X.σ 0 (yonedaEquiv x)
            have hface : leftHornEdgeSimplex.{u} (n + 1) =
                (Λ[n + 3, (0 : Fin (n + 3)).castSucc] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).toSSet.map
                  ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩
                    (by simp)).down).op
                  (horn.face (0 : Fin (n + 3)).castSucc
                    (Fin.last (n + 3))
                    (by simp [Fin.ext_iff])) := by
              have hL : (leftHornEdgeSimplex.{u} (n + 1)).1 =
                  stdSimplex.edge.{u} (n + 3) 0 ⟨1, by omega⟩ (by simp) :=
                rfl
              have hfaceval : (horn.face (0 : Fin (n + 3)).castSucc
                    (Fin.last (n + 3)) (by simp [Fin.ext_iff])).1 =
                  yonedaEquiv (stdSimplex.δ (Fin.last (n + 3))) := by
                have e1 : horn.face (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff]) =
                    yonedaEquiv (horn.ι (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff])) :=
                  (horn.yonedaEquiv_ι _ _ _).symm
                rw [e1]
                change (Λ[n + 2 + 1, (0 : Fin (n + 3)).castSucc] :
                      Subcomplex (Δ[n + 3] : SSet.{u})).ι.app _
                    (yonedaEquiv (horn.ι (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff]))) = _
                rw [← yonedaEquiv_comp]
                exact congrArg yonedaEquiv (horn.ι_ι _ _ _)
              have hR : ((Λ[n + 3, (0 : Fin (n + 3)).castSucc] :
                      Subcomplex (Δ[n + 3] : SSet.{u})).toSSet.map
                    ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩
                      (by simp)).down).op
                    (horn.face (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff]))).1 =
                  stdSimplex.edge.{u} (n + 3) 0 ⟨1, by omega⟩ (by simp) := by
                change (Δ[n + 3] : SSet.{u}).map
                    ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩
                      (by simp)).down).op
                    (horn.face (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff])).1 = _
                have hmap : (Δ[n + 3] : SSet.{u}).map
                      ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩ (by simp)).down).op
                      (yonedaEquiv (stdSimplex.δ (Fin.last (n + 3)))) =
                    ULift.up ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩
                        (by simp)).down ≫
                      SimplexCategory.δ (Fin.last (n + 3))) := rfl
                rw [hfaceval, hmap, mappingSpaceRight.edge01_comp_δ_last]
                exact rfl
              exact Subtype.ext (hL.trans hR.symm)
            have hnat : σ₀.app (op ⦋1⦌) (leftHornEdgeSimplex.{u} (n + 1)) =
                X.map ((stdSimplex.edge.{u} (n + 2) 0 ⟨1, by omega⟩
                    (by simp)).down).op
                  (σ₀.app (op ⦋n + 2⦌)
                    (horn.face (0 : Fin (n + 3)).castSucc
                      (Fin.last (n + 3)) (by simp [Fin.ext_iff]))) := by
              rw [hface]
              have hcongr := types_congr_hom
                (σ₀.naturality (op (stdSimplex.edge.{u} (n + 2) 0
                  ⟨1, by omega⟩ (by simp)).down))
                (horn.face (0 : Fin (n + 3)).castSucc (Fin.last (n + 3))
                  (by simp [Fin.ext_iff]))
              simp only [types_comp_apply] at hcongr
              exact hcongr
            have hσface : σ₀.app (op ⦋n + 2⦌)
                  (horn.face (0 : Fin (n + 3)).castSucc
                    (Fin.last (n + 3)) (by simp [Fin.ext_iff])) =
                yonedaEquiv (toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ x) := by
              have e1 : horn.face (0 : Fin (n + 3)).castSucc
                    (Fin.last (n + 3)) (by simp [Fin.ext_iff]) =
                  yonedaEquiv (horn.ι (0 : Fin (n + 3)).castSucc
                    (Fin.last (n + 3)) (by simp [Fin.ext_iff])) :=
                (horn.yonedaEquiv_ι _ _ _).symm
              rw [e1, ← yonedaEquiv_comp,
                hσ₀ (Fin.last (n + 3)) (by simp [Fin.ext_iff])]
              congr 1
              exact hg_last _
            have h1 : SSet.stdSimplex.map (SSet.stdSimplex.edge.{u} (n + 2) 0
                      ⟨1, by omega⟩ (by simp)).down ≫
                    toDeltaZero (Δ[n + 2] : SSet.{u}) =
                  toDeltaZero (Δ[1] : SSet.{u}) := toDeltaZero_eq _
            have h2 : toDeltaZero (Δ[1] : SSet.{u}) =
                  SSet.stdSimplex.map (SimplexCategory.σ (0 : Fin 1)) :=
                (toDeltaZero_eq _).symm
            rw [hnat, hσface, yonedaEquiv_naturality, ← Category.assoc,
              h1, h2]
            exact (yonedaEquiv_naturality
              (SimplexCategory.σ (0 : Fin 1)) x).symm
          have hid : (Edge.id (yonedaEquiv x)).edge =
              (leftHornEdge.{u} σ₀).edge := hed.symm
          exact (Edge.isEquivalence_iff_of_edge_eq hid).mp
            (Edge.isEquivalence_id _)
        obtain ⟨Φ, hΦeq⟩ :=
          (hasSpecialOuterHornFilling_of_quasicategory X).left σ₀ hedge
        refine ⟨Φ, fun k hk ↦ ?_⟩
        calc stdSimplex.δ k ≫ Φ
            = horn.ι (0 : Fin (n + 3)).castSucc k hk ≫
                ((Λ[n + 3, (0 : Fin (n + 3)).castSucc] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ) := by
              rw [← Category.assoc, horn.ι_ι]
          _ = horn.ι (0 : Fin (n + 3)).castSucc k hk ≫ σ₀ := by
              rw [show (Λ[n + 3, (0 : Fin (n + 3)).castSucc] :
                    Subcomplex (Δ[n + 3] : SSet.{u})).ι ≫ Φ = σ₀ from
                  hΦeq.symm]
          _ = g k hk := hσ₀ k hk
      · exact hcompat.exists_lift_of_quasicategory
          (by
            simp only [Fin.lt_def, Fin.val_zero, Fin.val_castSucc]
            exact Fin.pos_iff_ne_zero.mpr hi)
          (Fin.castSucc_lt_last i)
    -- The filler lies in the mapping space.
    have hΦfront : frontInclusion (n + 2) ≫ Φ =
        toDeltaZero (Δ[n + 2] : SSet.{u}) ≫ x := by
      rw [frontInclusion_eq,
        hΦ (Fin.last (n + 3)) (Fin.ne_of_gt (Fin.castSucc_lt_last i)),
        hg_last]
    have hΦright : rightVertex (n + 2) ≫ Φ = y := by
      obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (n + 3), j ≠ i := by
        by_cases hi : i = 0
        · exact ⟨1, by simp [hi]⟩
        · exact ⟨0, Ne.symm hi⟩
      calc rightVertex (n + 2) ≫ Φ
          = (rightVertex (n + 1) ≫ stdSimplex.δ j₀.castSucc) ≫ Φ := by
            rw [rightVertex_comp_δ_castSucc]
        _ = rightVertex (n + 1) ≫ (stdSimplex.δ j₀.castSucc ≫ Φ) :=
            Category.assoc _ _ _
        _ = rightVertex (n + 1) ≫ s j₀ hj₀ := by
            rw [hΦ j₀.castSucc (by
              simp only [ne_eq, Fin.castSucc_inj]
              exact hj₀), hg_castSucc j₀ hj₀]
        _ = y := hsright j₀ hj₀
    -- Assemble the filler in the mapping space.
    refine ⟨yonedaEquiv.symm
      ((mappingSpaceRight.simplexEquivSucc X x y (n + 2)).symm
        ⟨Φ, hΦfront, hΦright⟩), fun j hj ↦ ?_⟩
    rw [stdSimplex.δ_comp_yonedaEquiv_symm,
      show f j hj = yonedaEquiv.symm (yonedaEquiv (f j hj)) from
        (Equiv.symm_apply_apply _ _).symm]
    congr 1
    apply (mappingSpaceRight.simplexEquivSucc X x y (n + 1)).injective
    apply Subtype.ext
    rw [mappingSpaceRight.simplexEquivSucc_δ x y
      ((mappingSpaceRight.simplexEquivSucc X x y (n + 2)).symm
        ⟨Φ, hΦfront, hΦright⟩) j, Equiv.apply_symm_apply,
      hΦ j.castSucc (by
        simp only [ne_eq, Fin.castSucc_inj]
        exact hj), hg_castSucc j hj]

/-- Instance form of `SSet.kanComplex_mappingSpaceRight`. -/
instance (X : SSet.{u}) [Quasicategory X]
    (x y : (Δ[0] : SSet.{u}) ⟶ X) :
    KanComplex (mappingSpaceRight X x y) :=
  kanComplex_mappingSpaceRight X x y

end SSet

end

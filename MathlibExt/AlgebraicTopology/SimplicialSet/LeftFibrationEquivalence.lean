/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SliceLeftFibration
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLifting

/-!
# Equivalence lifting for left fibrations

Reusable conservativity and exact target-prescribed equivalence lifting for left fibrations.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet

/-- The source of a left fibration with quasicategory target is a
quasicategory. -/
theorem quasicategory_of_leftFibration {C D : SSet.{u}} (F : C ⟶ D)
    [LeftFibration F] [Quasicategory D] : Quasicategory C :=
  quasicategory_of_innerFibration F

/-- Yoneda faces: the Yoneda simplex of `δ i ≫ T` is `δ i` of the Yoneda
simplex of `T`. -/
private lemma yonedaEquiv_δ_comp {W : SSet.{u}} {n : ℕ}
    (T : (Δ[n + 1] : SSet.{u}) ⟶ W) (i : Fin (n + 2)) :
    yonedaEquiv (stdSimplex.δ i ≫ T) = W.δ i (yonedaEquiv T) := by
  conv_lhs => rw [← Equiv.symm_apply_apply yonedaEquiv T]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- Vertex 1 of a `2`-simplex, read through faces `d₀` then `d₂`. -/
private lemma δ_one_δ_zero_eq {W : SSet.{u}} (t : W _⦋2⦌) :
    W.δ 1 (W.δ 0 t) = W.δ 0 (W.δ 2 t) := by
  have hH : (0 : Fin 2).castSucc < (2 : Fin 3) := by decide
  have h := δ_comp_δ'_apply (S := W) (i := (0 : Fin 2)) (j := (2 : Fin 3)) hH t
  have e1 : (2 : Fin 3).pred hH.ne_zero = (1 : Fin 2) := rfl
  have e2 : (0 : Fin 2).castSucc = (0 : Fin 3) := rfl
  rw [e1, e2] at h
  exact h.symm

/-- Vertex 2 of a `2`-simplex, read through faces `d₀` then `d₁`. -/
private lemma δ_zero_δ_zero_eq {W : SSet.{u}} (t : W _⦋2⦌) :
    W.δ 0 (W.δ 0 t) = W.δ 0 (W.δ 1 t) := by
  have hH : (0 : Fin 3) = (0 : Fin 2).castSucc := by decide
  have h := δ_comp_δ_self'_apply (S := W) (i := (0 : Fin 2))
    (j := (0 : Fin 3)) hH t
  have e1 : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  rw [e1] at h
  exact h

/-- Right-inverse step for 019K: an edge over an inverse-carrying edge has a
right inverse, from a `Λ[2, 0]` lift of the `homInvId` triangle. -/
private theorem exists_compStruct_of_invStruct_map {C D : SSet.{u}}
    {F : C ⟶ D} [LeftFibration F] {x₀ x₁ : C _⦋0⦌} {e : Edge x₀ x₁}
    (J : Edge.InvStruct (e.map F)) :
    ∃ (ū : Edge x₁ x₀) (_ : Edge.CompStruct e ū (Edge.id x₀)),
      J.inv.edge = (ū.map F).edge := by
  -- The `Λ[2, 0]` face family: `d₁ ↦ id`-edge at `x₀`, `d₂ ↦ e`.
  let f : ∀ (j : Fin 3) (_ : j ≠ 0), (Δ[1] : SSet.{u}) ⟶ C := fun j _ =>
    if j = 1 then yonedaEquiv.symm (Edge.id x₀).edge
    else yonedaEquiv.symm e.edge
  have f1 : ∀ (h : (1 : Fin 3) ≠ 0),
      f 1 h = yonedaEquiv.symm (Edge.id x₀).edge := by
    intro _
    change (if (1 : Fin 3) = 1 then yonedaEquiv.symm (Edge.id x₀).edge
      else yonedaEquiv.symm e.edge) = _
    exact ite_eq_left rfl
  have f2 : ∀ (h : (2 : Fin 3) ≠ 0), f 2 h = yonedaEquiv.symm e.edge := by
    intro _
    change (if (2 : Fin 3) = 1 then yonedaEquiv.symm (Edge.id x₀).edge
      else yonedaEquiv.symm e.edge) = _
    exact ite_eq_right (by decide)
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
    have hj1 : j = 1 := by
      have h1 := j.is_lt
      have h2 := k.is_lt
      have hlt : j.val < k.val := hjk
      have hv : j.val = 1 := by omega
      exact Fin.ext hv
    have hk2 : k = 2 := by
      have h1 := j.is_lt
      have h2 := k.is_lt
      have hlt : j.val < k.val := hjk
      have hv : k.val = 2 := by omega
      exact Fin.ext hv
    subst hj1
    subst hk2
    have e1 : (2 : Fin 3).pred (Fin.ne_zero_of_lt hjk) = 1 := rfl
    have e2 : (1 : Fin 3).castPred (Fin.ne_last_of_lt hjk) = 1 := rfl
    have g1 : f 1 hj = yonedaEquiv.symm (Edge.id x₀).edge := f1 hj
    have g2 : f 2 hk = yonedaEquiv.symm e.edge := f2 hk
    rw [e1, e2, g1, g2, stdSimplex.δ_comp_yonedaEquiv_symm,
      stdSimplex.δ_comp_yonedaEquiv_symm]
    congr 1
    rw [(Edge.id x₀).src_eq, e.src_eq]
  -- Bottom: the `homInvId` triangle in `D`.
  set b : (Δ[2] : SSet.{u}) ⟶ D :=
    yonedaEquiv.symm J.homInvId.simplex with hb
  have comm : ∀ (j : Fin 3) (hj : j ≠ 0),
      f j hj ≫ F = stdSimplex.δ j ≫ b := by
    intro j hj
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hcases : j = 1 ∨ j = 2 := by
      have h1 := j.is_lt
      have hv : j.val = 1 ∨ j.val = 2 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    rcases hcases with rfl | rfl
    · rw [f1 hj, hb, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      rw [← Edge.map_edge, Edge.map_id]
      exact J.homInvId.d₁.symm
    · rw [f2 hj, hb, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      rw [← Edge.map_edge]
      exact J.homInvId.d₂.symm
  have hp : HasLiftingProperty Λ[2, (0 : Fin 3)].ι F :=
    LeftFibration.hasLiftingProperty_horn
      (show (0 : Fin 3) < Fin.last 2 by decide)
  obtain ⟨T, hTfaces, hTF⟩ := exists_simplex_lift_horn hf hp b comm
  -- Normalize faces to `Fin 3` (defeq to `Fin (1 + 2)`, but rewriting needs
  -- syntactic form), pre-instantiated to avoid `∀`-rewrite side goals.
  have hTfaces3 : ∀ (j : Fin 3) (hj : j ≠ 0),
      stdSimplex.δ j ≫ T = f j hj := hTfaces
  have hTf2 : stdSimplex.δ 2 ≫ T = yonedaEquiv.symm e.edge := by
    rw [hTfaces3 2 (by decide)]
    exact f2 (by decide)
  have hTf1 : stdSimplex.δ 1 ≫ T =
      yonedaEquiv.symm (Edge.id x₀).edge := by
    rw [hTfaces3 1 (by decide)]
    exact f1 (by decide)
  -- `ū := d₀(T)`; its endpoints are read off faces `d₂`, `d₁`.
  have hsrc : C.δ 1 (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) = x₁ := by
    rw [yonedaEquiv_δ_comp, δ_one_δ_zero_eq, ← yonedaEquiv_δ_comp,
      hTf2, Equiv.apply_symm_apply, e.tgt_eq]
  have htgt : C.δ 0 (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) = x₀ := by
    rw [yonedaEquiv_δ_comp, δ_zero_δ_zero_eq, ← yonedaEquiv_δ_comp,
      hTf1, Equiv.apply_symm_apply]
    exact (Edge.id x₀).tgt_eq
  refine ⟨Edge.mk (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) hsrc htgt,
    Edge.CompStruct.mk (yonedaEquiv T) ?_ ?_ ?_, ?_⟩
  · rw [← yonedaEquiv_δ_comp, hTf2, Equiv.apply_symm_apply]
  · change C.δ 0 (yonedaEquiv T) =
        yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)
    rw [yonedaEquiv_δ_comp]
  · rw [← yonedaEquiv_δ_comp, hTf1, Equiv.apply_symm_apply]
  · calc J.inv.edge = D.δ 0 J.homInvId.simplex := J.homInvId.d₀.symm
      _ = ((Edge.mk (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) hsrc htgt).map
          F).edge := by
        rw [Edge.map_edge]
        change D.δ 0 J.homInvId.simplex =
          F.app _ (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T))
        rw [← yonedaEquiv_comp, Category.assoc, hTF, hb,
          stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]

/-- **(Kerodon 019K, Proposition 4.4.2.11, target-QC-only weakening).** A left
fibration with quasicategory target reflects equivalences. -/
theorem LeftFibration.isEquivalence_of_map {C D : SSet.{u}} {F : C ⟶ D}
    [LeftFibration F] [Quasicategory D] {x₀ x₁ : C _⦋0⦌} {e : Edge x₀ x₁}
    (h : (e.map F).IsEquivalence) : e.IsEquivalence := by
  obtain ⟨J⟩ := h.nonempty_invStruct
  obtain ⟨ū, c₁, hF⟩ := exists_compStruct_of_invStruct_map (F := F) (e := e) J
  have J' : Edge.InvStruct (ū.map F) := J.invStructInv.ofEq hF
  obtain ⟨w, c₂, -⟩ := exists_compStruct_of_invStruct_map (F := F) (e := ū) J'
  have h1 : e.toHoHom ≫ ū.toHoHom = 𝟙 _ := by
    rw [Edge.toHoHom_comp c₁, Edge.toHoHom_id]
  have h2 : ū.toHoHom ≫ w.toHoHom = 𝟙 _ := by
    rw [Edge.toHoHom_comp c₂, Edge.toHoHom_id]
  have hgf : ū.toHoHom ≫ e.toHoHom = 𝟙 _ := by
    calc ū.toHoHom ≫ e.toHoHom
        = (ū.toHoHom ≫ e.toHoHom) ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = (ū.toHoHom ≫ e.toHoHom) ≫ (ū.toHoHom ≫ w.toHoHom) := by rw [h2]
      _ = 𝟙 _ := by
        rw [Category.assoc, ← Category.assoc e.toHoHom, h1,
          Category.id_comp, h2]
  change IsIso e.toHoHom
  exact ⟨ū.toHoHom, h1, hgf⟩

/-- A left fibration with quasicategory target has strict source-prescribed
equivalence-edge lifting. The lifted edge retains its target equality and its
exact image simplex. -/
theorem hasStrictEquivalenceLifting_of_leftFibration {C D : SSet.{u}}
    (F : C ⟶ D) [LeftFibration F] [Quasicategory D] :
    HasStrictEquivalenceLifting F := by
  apply (hasStrictEquivalenceLifting_iff F).2
  intro x₀ y₁ g hg
  have hf : horn.IsCompatible
      (fun (j : Fin 2) (_ : j ≠ 0) ↦ yonedaEquiv.symm x₀) := by
    rw [horn.isCompatible_zero_iff_true]
    trivial
  set b : (Δ[1] : SSet.{u}) ⟶ D := yonedaEquiv.symm g.edge with hb
  have comm : ∀ (j : Fin 2) (hj : j ≠ 0),
      yonedaEquiv.symm x₀ ≫ F = stdSimplex.δ j ≫ b := by
    intro j hj
    have hj1 : j = 1 := by
      apply Fin.ext
      have hj0 : j.val ≠ 0 := fun h ↦ hj (Fin.ext h)
      omega
    subst j
    rw [yonedaEquiv_symm_comp, hb,
      stdSimplex.δ_comp_yonedaEquiv_symm, g.src_eq]
  have hp : HasLiftingProperty Λ[1, (0 : Fin 2)].ι F :=
    LeftFibration.hasLiftingProperty_horn
      (show (0 : Fin 2) < Fin.last 1 by decide)
  obtain ⟨β, hβfaces, hβF⟩ := exists_simplex_lift_horn hf hp b comm
  have hβfaces2 : ∀ (j : Fin 2) (hj : j ≠ 0),
      stdSimplex.δ j ≫ β = yonedaEquiv.symm x₀ := hβfaces
  set x₁ : C _⦋0⦌ := yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ β) with hx₁def
  have hx₁ : F.app _ x₁ = y₁ := by
    rw [hx₁def, ← yonedaEquiv_comp, Category.assoc, hβF, hb,
      stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply,
      g.tgt_eq]
  have hsrc : C.δ 1 (yonedaEquiv β) = x₀ := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hβfaces2 1 (by decide),
      Equiv.apply_symm_apply]
  have htgt : C.δ 0 (yonedaEquiv β) = x₁ := by
    rw [hx₁def, stdSimplex.yonedaEquiv_δ_comp]
  set f : Edge x₀ x₁ := Edge.mk (yonedaEquiv β) hsrc htgt with hfdef
  have hmap : (f.map F).edge = g.edge := by
    rw [Edge.map_edge, hfdef]
    change F.app _ (yonedaEquiv β) = g.edge
    rw [← yonedaEquiv_comp, hβF, hb, Equiv.apply_symm_apply]
  have hfEquiv : f.IsEquivalence := by
    apply LeftFibration.isEquivalence_of_map (F := F) (e := f)
    exact (Edge.isEquivalence_iff_of_edge_eq hmap).2 hg
  exact ⟨x₁, hx₁, f, hfEquiv, hmap⟩

/-!
### §5. Target-prescribed exact iso lifting (Kerodon 01EW, inlined)

Example 4.4.1.11 says a left fibration of ∞-categories is an isofibration; we
inline only the target-prescribed instance needed for 01H0 step 11 (no
isofibration API is developed). Given an equivalence edge `u` in `D` and a
vertex `y₁` in `C` over its target: lift `u⁻¹` via `Λ[1, 0]` to `β` starting
at `y₁`, then lift the `invHomId` triangle via `Λ[2, 0]` with faces
`d₁ ↦ id`, `d₂ ↦ β` to `T`; `ū := d₀(T)` lies over `u` EXACTLY (exactness
comes from the base triangle, not from prescribing `ū`), ends at `y₁`, and
is an equivalence by §4.
-/

/-- **(Kerodon 01EW, Example 4.4.1.11, target-prescribed exact form).** Exact
iso-lifting with prescribed target along a left fibration with quasicategory
target. -/
theorem LeftFibration.exists_isoLift_target {C D : SSet.{u}} {F : C ⟶ D}
    [LeftFibration F] [Quasicategory D]
    {d₀ d₁ : D _⦋0⦌} {u : Edge d₀ d₁} (hu : u.IsEquivalence)
    {y₁ : C _⦋0⦌} (hy₁ : F.app _ y₁ = d₁) :
    ∃ (y₀ : C _⦋0⦌) (_ : F.app _ y₀ = d₀) (ū : Edge y₀ y₁)
      (_ : ū.IsEquivalence), (ū.map F).edge = u.edge := by
  obtain ⟨I⟩ := hu.nonempty_invStruct
  -- Step 1: lift `u⁻¹` via `Λ[1, 0]` to `β` starting at `y₁`.
  have hfβ : horn.IsCompatible
      (fun (j : Fin 2) (_ : j ≠ 0) => yonedaEquiv.symm y₁) := by
    rw [horn.isCompatible_zero_iff_true]
    trivial
  set bβ : (Δ[1] : SSet.{u}) ⟶ D :=
    yonedaEquiv.symm I.inv.edge with hbβ
  have commβ : ∀ (j : Fin 2) (hj : j ≠ 0),
      yonedaEquiv.symm y₁ ≫ F = stdSimplex.δ j ≫ bβ := by
    intro j hj
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hj1 : j = 1 := by
      have h1 := j.is_lt
      have hv : j.val = 1 := by omega
      exact Fin.ext hv
    subst hj1
    rw [yonedaEquiv_symm_comp, hbβ, stdSimplex.δ_comp_yonedaEquiv_symm,
      hy₁, I.inv.src_eq]
  have hpβ : HasLiftingProperty Λ[1, (0 : Fin 2)].ι F :=
    LeftFibration.hasLiftingProperty_horn
      (show (0 : Fin 2) < Fin.last 1 by decide)
  obtain ⟨β, hβfaces, hβF⟩ := exists_simplex_lift_horn hfβ hpβ bβ commβ
  have hβfaces2 : ∀ (j : Fin 2) (hj : j ≠ 0),
      stdSimplex.δ j ≫ β = yonedaEquiv.symm y₁ := hβfaces
  -- The source vertex `y₀` of the lift: the target vertex of `β`.
  set y₀ : C _⦋0⦌ := yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ β) with hy₀def
  have hy₀ : F.app _ y₀ = d₀ := by
    rw [hy₀def, ← yonedaEquiv_comp, Category.assoc, hβF, hbβ,
      stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.apply_symm_apply]
    exact I.inv.tgt_eq
  -- Step 2: lift the `invHomId` triangle via `Λ[2, 0]`.
  let f : ∀ (j : Fin 3) (_ : j ≠ 0), (Δ[1] : SSet.{u}) ⟶ C := fun j _ =>
    if j = 1 then yonedaEquiv.symm (Edge.id y₁).edge else β
  have f1 : ∀ (h : (1 : Fin 3) ≠ 0),
      f 1 h = yonedaEquiv.symm (Edge.id y₁).edge := by
    intro _
    change (if (1 : Fin 3) = 1 then yonedaEquiv.symm (Edge.id y₁).edge
      else β) = _
    exact ite_eq_left rfl
  have f2 : ∀ (h : (2 : Fin 3) ≠ 0), f 2 h = β := by
    intro _
    change (if (2 : Fin 3) = 1 then yonedaEquiv.symm (Edge.id y₁).edge
      else β) = _
    exact ite_eq_right (by decide)
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
    have hj1 : j = 1 := by
      have h1 := j.is_lt
      have h2 := k.is_lt
      have hlt : j.val < k.val := hjk
      have hv : j.val = 1 := by omega
      exact Fin.ext hv
    have hk2 : k = 2 := by
      have h1 := j.is_lt
      have h2 := k.is_lt
      have hlt : j.val < k.val := hjk
      have hv : k.val = 2 := by omega
      exact Fin.ext hv
    subst hj1
    subst hk2
    have e1 : (2 : Fin 3).pred (Fin.ne_zero_of_lt hjk) = 1 := rfl
    have e2 : (1 : Fin 3).castPred (Fin.ne_last_of_lt hjk) = 1 := rfl
    have g1 : f 1 hj = yonedaEquiv.symm (Edge.id y₁).edge := f1 hj
    have g2 : f 2 hk = β := f2 hk
    rw [e1, e2, g1, g2, stdSimplex.δ_comp_yonedaEquiv_symm,
      hβfaces2 1 (by decide)]
    congr 1
    -- Source of `id`-edge (`y₁`) = source of `β` (`δ 1 ≫ β = y₁`).
    exact (Edge.id y₁).src_eq
  set b : (Δ[2] : SSet.{u}) ⟶ D :=
    yonedaEquiv.symm I.invHomId.simplex with hb
  have comm : ∀ (j : Fin 3) (hj : j ≠ 0),
      f j hj ≫ F = stdSimplex.δ j ≫ b := by
    intro j hj
    have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hcases : j = 1 ∨ j = 2 := by
      have h1 := j.is_lt
      have hv : j.val = 1 ∨ j.val = 2 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    rcases hcases with rfl | rfl
    · rw [f1 hj, hb, yonedaEquiv_symm_comp,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      rw [← Edge.map_edge, Edge.map_id, hy₁]
      exact I.invHomId.d₁.symm
    · rw [f2 hj, hβF, hb, hbβ, stdSimplex.δ_comp_yonedaEquiv_symm]
      congr 1
      exact I.invHomId.d₂.symm
  have hp : HasLiftingProperty Λ[2, (0 : Fin 3)].ι F :=
    LeftFibration.hasLiftingProperty_horn
      (show (0 : Fin 3) < Fin.last 2 by decide)
  obtain ⟨T, hTfaces, hTF⟩ := exists_simplex_lift_horn hf hp b comm
  have hTfaces3 : ∀ (j : Fin 3) (hj : j ≠ 0),
      stdSimplex.δ j ≫ T = f j hj := hTfaces
  have hTf2 : stdSimplex.δ 2 ≫ T = β := by
    rw [hTfaces3 2 (by decide)]
    exact f2 (by decide)
  have hTf1 : stdSimplex.δ 1 ≫ T =
      yonedaEquiv.symm (Edge.id y₁).edge := by
    rw [hTfaces3 1 (by decide)]
    exact f1 (by decide)
  -- `ū := d₀(T)`: exact over `u`, target `y₁`, source `y₀`.
  have hexact : (stdSimplex.δ (0 : Fin 3) ≫ T) ≫ F =
      yonedaEquiv.symm u.edge := by
    rw [Category.assoc, hTF, hb, stdSimplex.δ_comp_yonedaEquiv_symm]
    congr 1
    exact I.invHomId.d₀
  have hsrc : C.δ 1 (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) = y₀ := by
    rw [yonedaEquiv_δ_comp, δ_one_δ_zero_eq, ← yonedaEquiv_δ_comp, hTf2,
      ← yonedaEquiv_δ_comp, hy₀def]
  have htgt : C.δ 0 (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) = y₁ := by
    rw [yonedaEquiv_δ_comp, δ_zero_δ_zero_eq, ← yonedaEquiv_δ_comp,
      hTf1, Equiv.apply_symm_apply]
    exact (Edge.id y₁).tgt_eq
  set ū : Edge y₀ y₁ :=
    Edge.mk (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) hsrc htgt with hūdef
  have hmap : (ū.map F).edge = u.edge := by
    rw [Edge.map_edge, hūdef]
    change F.app _ (yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T)) = u.edge
    rw [← yonedaEquiv_comp, hexact, Equiv.apply_symm_apply]
  have hūEquiv : ū.IsEquivalence := by
    have hmapEquiv : (ū.map F).IsEquivalence :=
      (Edge.isEquivalence_iff_of_edge_eq hmap).mpr hu
    exact LeftFibration.isEquivalence_of_map hmapEquiv
  exact ⟨y₀, hy₀, ū, hūEquiv, hmap⟩


end SSet

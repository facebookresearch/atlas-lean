/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWBoundaryRLP
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc

/-!
# Boundary lifting between Kan complexes

For a map p:E→B between Kan simplicial sets in universe u, right lifting against every boundary
inclusion ∂Δ[n]→Δ[n], n≥0, implies simplicial weak equivalence. With the additional fibration
hypothesis, weak equivalence and boundary lifting are equivalent.

The proof uses strict fibers and the pointed fibration-sequence connecting maps.

Reference: Goerss and Jardine, Simplicial Homotopy Theory, Chapter I.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial SSet HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

private lemma fibration_of_rlp_I {X Y : SSet.{u}} {p : X ⟶ Y}
    (hp : modelCategoryQuillen.I.{u}.rlp p) : Fibration p := by
  rw [modelCategoryQuillen.fibration_iff]
  apply MorphismProperty.antitone_rlp modelCategoryQuillen.J_le_monomorphisms
  rwa [SSet.rlp_monomorphisms]

private theorem nonempty_zero_of_rlp_I {F : SSet.{u}} {q : F ⟶ Δ[0]}
    (hq : modelCategoryQuillen.I.{u}.rlp q) : Nonempty (F _⦋0⦌) := by
  let hinit : IsInitial ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) :=
    (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
      (Subcomplex.eqToIso boundary_zero).symm
  let top : (boundary 0 : SSet.{u}) ⟶ F := hinit.to F
  let sq : CommSq top (boundary 0).ι q (𝟙 _) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have : HasLiftingProperty (boundary 0).ι q :=
    hq _ (modelCategoryQuillen.boundary_ι_mem_I 0)
  exact ⟨yonedaEquiv sq.lift⟩

private theorem subsingleton_π₀_of_rlp_I {F : SSet.{u}} {q : F ⟶ Δ[0]}
    (hq : modelCategoryQuillen.I.{u}.rlp q) : Subsingleton (π₀ F) where
  allEq a b := by
    obtain ⟨x₀, rfl⟩ := a.mk_surjective
    obtain ⟨x₁, rfl⟩ := b.mk_surjective
    let faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ F) := fun i ↦
      if i = 1 then yonedaEquiv.symm x₀ else yonedaEquiv.symm x₁
    have hfaces : boundary.IsCompatible faces := True.intro
    let top : (boundary 1 : SSet.{u}) ⟶ F := hfaces.desc
    have htop₀ : boundary.ι (1 : Fin 2) ≫ top = yonedaEquiv.symm x₀ := by
      simp [top, faces]
    have htop₁ : boundary.ι (0 : Fin 2) ≫ top = yonedaEquiv.symm x₁ := by
      simp [top, faces]
    let sq : CommSq top (boundary 1).ι q (stdSimplex.isTerminalObj₀.from _) :=
      ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
    have : HasLiftingProperty (boundary 1).ι q :=
      hq _ (modelCategoryQuillen.boundary_ι_mem_I 1)
    apply π₀.sound
    exact Edge.mk (yonedaEquiv sq.lift)
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply,
          ← boundary.ι_ι_assoc, sq.fac_left, htop₀]))
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply,
          ← boundary.ι_ι_assoc, sq.fac_left, htop₁]))

private theorem subsingleton_π_of_rlp_I {F : SSet.{u}} {q : F ⟶ Δ[0]}
    (hq : modelCategoryQuillen.I.{u}.rlp q) (n : ℕ) (x : F _⦋0⦌) :
    Subsingleton (KanComplex.π n F x) := by
  let _ : Fibration q := fibration_of_rlp_I hq
  let _ : KanComplex (Δ[0] : SSet.{u}) := by
    exact (HomotopicalAlgebra.isFibrant_iff_of_isTerminal (𝟙 _)
      stdSimplex.isTerminalObj₀).2 (by infer_instance)
  let _ : KanComplex F := isFibrant_of_fibration q
  obtain _ | m := n
  · rw [← (KanComplex.π₀EquivπZero x).subsingleton_congr]
    exact subsingleton_π₀_of_rlp_I hq
  · constructor
    intro a b
    have all_eq_one : ∀ c : KanComplex.π (m + 1) F x, c = 1 := by
      intro c
      obtain ⟨s, rfl⟩ := c.mk_surjective
      let faces : Fin (m + 3) → ((Δ[m + 1] : SSet.{u}) ⟶ F) := fun i ↦
        if i = 0 then SSet.RelativeMorphism.map s else SSet.const x
      have hfaces : boundary.IsCompatible faces := by
        rw [boundary.isCompatible_succ_iff]
        intro j k hjk
        by_cases hj : j = 0
        · subst j
          have hk : k ≠ 0 := Fin.ne_zero_of_lt hjk
          simp [faces, hk, s.δ_map, SSet.comp_const]
        · have hk : k ≠ 0 := Fin.ne_zero_of_lt hjk
          simp [faces, hj, hk, SSet.comp_const]
      let top : (boundary (m + 2) : SSet.{u}) ⟶ F := hfaces.desc
      let sq : CommSq top (boundary (m + 2)).ι q
          (stdSimplex.isTerminalObj₀.from _) :=
        ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
      have : HasLiftingProperty (boundary (m + 2)).ι q :=
        hq _ (modelCategoryQuillen.boundary_ι_mem_I (m + 2))
      rw [KanComplex.π.mk_eq_one_iff]
      refine ⟨{
        map := sq.lift
        δ_castSucc_map := ?_
        δ_succ_map := ?_
        δ_map_of_lt := ?_
        δ_map_of_gt := ?_ }⟩
      · change stdSimplex.δ 0 ≫ sq.lift = SSet.RelativeMorphism.map s
        rw [← boundary.ι_ι_assoc, sq.fac_left,
          hfaces.ι_desc]
        simp [faces]
      · change stdSimplex.δ 1 ≫ sq.lift = SSet.const x
        rw [← boundary.ι_ι_assoc, sq.fac_left,
          hfaces.ι_desc]
        simp [faces]
      · intro j hj
        simp at hj
      · intro j hj
        rw [← boundary.ι_ι_assoc, sq.fac_left,
          hfaces.ι_desc]
        have hj₀ : j ≠ 0 := by
          intro h
          subst j
          exact (Fin.not_lt_zero _ hj)
        simp [faces, hj₀]
    exact (all_eq_one a).trans (all_eq_one b).symm

private theorem fiber_rlp_I {E B : SSet.{u}} {p : E ⟶ B}
    (hp : modelCategoryQuillen.I.{u}.rlp p)
    (b : B.obj (Opposite.op (SimplexCategory.mk 0))) :
    modelCategoryQuillen.I.{u}.rlp
      (stdSimplex.isTerminalObj₀.from (Subcomplex.fiber p b : SSet.{u})) :=
  MorphismProperty.of_isPullback (Subcomplex.fiber_isPullback p b) hp

private theorem nonempty_edge_of_π₀_eq {B : SSet.{u}}
    [KanComplex B]
    {b₀ b₁ : B.obj (Opposite.op (SimplexCategory.mk 0))}
    (h : π₀.mk b₀ = π₀.mk b₁) :
    Nonempty (Edge b₀ b₁) := by
  classical
  rw [π₀.mk_eq_mk_iff] at h
  induction h with
  | rel _ _ h => exact h
  | refl => exact ⟨Edge.id _⟩
  | symm _ _ _ ih => exact ⟨ih.some.inv⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.comp ih₂.some⟩

private theorem bijective_mapπ₀_of_rlp_I
    {E B : SSet.{u}} {p : E ⟶ B} [KanComplex B]
    (hp : modelCategoryQuillen.I.{u}.rlp p) :
    Function.Bijective (mapπ₀ p) := by
  classical
  constructor
  · intro a b hab
    obtain ⟨e₀, rfl⟩ := a.mk_surjective
    obtain ⟨e₁, rfl⟩ := b.mk_surjective
    rw [mapπ₀_mk, mapπ₀_mk] at hab
    obtain ⟨edge⟩ := nonempty_edge_of_π₀_eq hab
    let faces : Fin 2 → ((Δ[0] : SSet.{u}) ⟶ E) := fun i ↦
      if i = 1 then yonedaEquiv.symm e₀ else yonedaEquiv.symm e₁
    have hfaces : boundary.IsCompatible faces := True.intro
    let top : (boundary 1 : SSet.{u}) ⟶ E := hfaces.desc
    have htop₀ : boundary.ι (1 : Fin 2) ≫ top = yonedaEquiv.symm e₀ := by
      simp [top, faces]
    have htop₁ : boundary.ι (0 : Fin 2) ≫ top = yonedaEquiv.symm e₁ := by
      simp [top, faces]
    let bottom : (Δ[1] : SSet.{u}) ⟶ B := yonedaEquiv.symm edge.edge
    let sq : CommSq top (boundary 1).ι p bottom := ⟨by
      apply boundary.hom_ext
      intro i
      fin_cases i
      · change (boundary.ι (0 : Fin 2) ≫ top) ≫ p =
          (boundary.ι (0 : Fin 2) ≫ (boundary 1).ι) ≫ bottom
        rw [htop₁, yonedaEquiv_symm_comp, boundary.ι_ι]
        simp only [bottom, stdSimplex.δ_comp_yonedaEquiv_symm,
          edge.tgt_eq]
      · change (boundary.ι (1 : Fin 2) ≫ top) ≫ p =
          (boundary.ι (1 : Fin 2) ≫ (boundary 1).ι) ≫ bottom
        rw [htop₀, yonedaEquiv_symm_comp, boundary.ι_ι]
        simp only [bottom, stdSimplex.δ_comp_yonedaEquiv_symm,
          edge.src_eq]⟩
    have : HasLiftingProperty (boundary 1).ι p :=
      hp _ (modelCategoryQuillen.boundary_ι_mem_I 1)
    apply π₀.sound
    exact Edge.mk (yonedaEquiv sq.lift)
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply,
          ← boundary.ι_ι_assoc, sq.fac_left, htop₀]))
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply,
          ← boundary.ι_ι_assoc, sq.fac_left, htop₁]))
  · intro b
    obtain ⟨b, rfl⟩ := b.mk_surjective
    let hinit : IsInitial ((boundary 0 : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u}) :=
      (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))).ofIso
        (Subcomplex.eqToIso boundary_zero).symm
    let top : (boundary 0 : SSet.{u}) ⟶ E := hinit.to E
    let sq : CommSq top (boundary 0).ι p (yonedaEquiv.symm b) :=
      ⟨boundary.hom_ext₀⟩
    have : HasLiftingProperty (boundary 0).ι p :=
      hp _ (modelCategoryQuillen.boundary_ι_mem_I 0)
    refine ⟨π₀.mk (yonedaEquiv sq.lift), ?_⟩
    rw [mapπ₀_mk]
    congr 1
    rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

private lemma π_group_one_eq_one {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    @One.one (KanComplex.π (n + 1) X x)
      ((inferInstance :
        Group (KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.toOne) = 1 := by
  let gOne : KanComplex.π (n + 1) X x := @One.one _
    ((inferInstance :
      Group (KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
  let d : KanComplex.π (n + 1) X x := KanComplex.π.mk
    (RelativeMorphism.const : X.PtSimplex (n + 1) x)
  have hd : d * gOne = gOne := by
    obtain ⟨s, hs⟩ := gOne.mk_surjective
    rw [← hs]
    exact (KanComplex.π.mul_mk_eq_iff).2
      ⟨PtSimplex.MulStruct.oneMul s (Fin.last n)⟩
  change gOne = 1
  calc
    gOne = d * gOne := hd.symm
    _ = d := ((inferInstance :
      Group (KanComplex.π (n + 1) X x)).toDivInvMonoid.toMonoid.toMulOneClass.mul_one d)
    _ = 1 := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem bijective_piMap_succ_of_rlp_I
    {E B : SSet.{u}} {p : E ⟶ B} [KanComplex E] [KanComplex B]
    (hp : modelCategoryQuillen.I.{u}.rlp p) (n : ℕ)
    (e : E.obj (Opposite.op (SimplexCategory.mk 0))) :
    Function.Bijective (KanComplex.π.map (x := e)
      (y := p.app _ e) p rfl (n + 1)) := by
  let S : FibrationSequence.{u} :=
    { E := E
      B := B
      p := p
      fibration_p := fibration_of_rlp_I hp
      fibrant_B := inferInstance
      e := e
      b := p.app _ e
      hb := rfl }
  have hsub (k : ℕ) :
      Subsingleton (KanComplex.π k S.fiber S.fiberPoint) :=
    subsingleton_π_of_rlp_I (fiber_rlp_I hp S.b) k S.fiberPoint
  constructor
  · let oneE : KanComplex.π (n + 1) S.E S.e := @One.one _
      ((inferInstance :
        Group (KanComplex.π (n + 1) S.E S.e)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
    let oneB : KanComplex.π (n + 1) S.B S.b := @One.one _
      ((inferInstance :
        Group (KanComplex.π (n + 1) S.B S.b)).toDivInvMonoid.toMonoid.toMulOneClass.toOne)
    let φ : KanComplex.π (n + 1) S.E S.e →*
        KanComplex.π (n + 1) S.B S.b :=
      { toFun := KanComplex.π.map S.p S.hb (n + 1)
        map_one' := by
          change KanComplex.π.map S.p S.hb (n + 1) oneE = oneB
          rw [show oneE = 1 from π_group_one_eq_one n S.e,
            show oneB = 1 from π_group_one_eq_one n S.b]
          exact KanComplex.π.map_one S.p S.hb (n + 1)
        map_mul' := KanComplex.π.map_mul S.p S.hb n }
    change Function.Injective φ
    rw [injective_iff_map_eq_one]
    intro q hq
    change KanComplex.π.map S.p S.hb (n + 1) q = oneB at hq
    have hq' : KanComplex.π.map S.p S.hb (n + 1) q = 1 := by
      exact hq.trans (π_group_one_eq_one n S.b)
    obtain ⟨r, hr⟩ := S.exactness_at_E q hq'
    have hr₁ : r = 1 := Subsingleton.elim _ _
    change q = oneE
    calc
      q = 1 := by rw [← hr, hr₁, KanComplex.π.map_one]
      _ = oneE := (π_group_one_eq_one n S.e).symm
  · intro q
    have hq : S.connectingMap n q = 1 := Subsingleton.elim _ _
    exact S.exactness_at_B q hq

namespace KanComplex

/-- For Kan simplicial sets E,B in universe u and p:E→B, right lifting against every ∂Δ[n]→Δ[n],
n≥0, implies that p is a simplicial weak equivalence: it induces a bijection on connected
components and isomorphisms on pointed homotopy groups. -/
theorem W.of_rlp_I {E B : SSet.{u}} {p : E ⟶ B}
    [KanComplex E] [KanComplex B]
    (hp : modelCategoryQuillen.I.{u}.rlp p) : W.{u} p :=
  (W_iff p).2 ⟨bijective_mapπ₀_of_rlp_I hp,
    fun n e ↦ bijective_piMap_succ_of_rlp_I hp n e⟩

/-- For a simplicial fibration p:E→B between Kan simplicial sets in universe u, p lifts against
every boundary inclusion ∂Δ[n]→Δ[n], n≥0, if and only if p is a simplicial weak equivalence. -/
theorem I_rlp_iff_W_of_fibration {E B : SSet.{u}} (p : E ⟶ B)
    [KanComplex E] [KanComplex B] [Fibration p] :
    modelCategoryQuillen.I.{u}.rlp p ↔ W.{u} p := by
  constructor
  · exact W.of_rlp_I
  · intro hpW
    exact modelCategoryQuillen.J_rlp_inf_W_le_I_rlp p
      ⟨(modelCategoryQuillen.fibration_iff p).1 (by infer_instance), hpW⟩

/-- For every universe u, all Kan simplicial sets X,Y and every f:X→Y, boundary lifting against
∂Δ[n]→Δ[n] for every n≥0 implies simplicial weak equivalence. The Kan hypotheses on both source
and target are part of this implication. -/
theorem I_rlp_to_W_kanRestricted :
    ∀ {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] {f : X ⟶ Y},
      modelCategoryQuillen.I.{u}.rlp f → W.{u} f :=
  fun hf ↦ W.of_rlp_I hf

end KanComplex

end SSet

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationFibration
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationPullbackMono
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedHomotopyEquiv
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

/-!
# Realization and singular images of pointed fibration sequences

A strict sequence consists of a Kan fibration p:E→B with Kan base B, compatible vertices e,b and
strict fiber F_b. Applying U=Sing∘realization gives another pointed Kan-fibration sequence, with
total and base points ηE(e),ηB(b).

The strict-fiber comparison χ:U(F_b)≅fiber(U(p)) commutes with inclusion into U(E). The map of
fibers induced by the unit is η(F_b) followed by χ, and this composite preserves the chosen
fiber point.

For a Kan complex X and vertex x, every connecting map of the U-image of its loop fibration
sequence is bijective: π(n+1)(U(X),ηx)→πn(F′,e′), where F′ is the image sequence's strict fiber.
All constructions preserve the arbitrary simplicial-set universe u.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
  Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

noncomputable section
universe u

namespace SSet.FibrationSequence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. Applying U to E,B,p and η to the chosen vertices gives the pointed
realization-and-singular fibration sequence. -/
noncomputable def realSingSequence
    (S : FibrationSequence.{u}) : FibrationSequence.{u} where
  E := (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.E
  B := (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.B
  p := (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.p
  fibration_p := by
    let _ : Fibration S.p := S.fibration_p
    rw [SSet.modelCategoryQuillen.fibration_iff]
    exact (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp
      (SSet.toTop_map_mem_realizedHornRLP S.p)
  fibrant_B := TopCat.toSSet_obj_kanComplex _
  e := (sSetTopAdj.unit.app S.E).app _ S.e
  b := (sSetTopAdj.unit.app S.B).app _ S.b
  hb := by
    have h := congrArg
      (fun f : S.E ⟶
        (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.B =>
          f.app (op ⦋0⦌) S.e)
      (sSetTopAdj.unit.naturality S.p)
    simpa only [NatTrans.comp_app, types_comp_apply, Functor.id_map,
      S.hb] using h.symm

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. The unit maps ηE,ηB form a morphism from the original pointed fibration sequence to its
U-image, commuting with p and preserving both vertices. -/
noncomputable def unitSequenceHom (S : FibrationSequence.{u}) :
    FibrationSequenceHom S S.realSingSequence where
  totalMap := sSetTopAdj.unit.app S.E
  baseMap := sSetTopAdj.unit.app S.B
  comm := (sSetTopAdj.unit.naturality S.p).symm
  total_pt := rfl
  base_pt := rfl

private noncomputable def realizedZeroIsTerminal :
    IsTerminal (SSet.toTop.obj (Δ[0] : SSet.{u})) := by
  let _ : ∀ Y : TopCat.{u}, Unique
      (Y ⟶ SSet.toTop.obj (Δ[0] : SSet.{u})) := fun Y =>
    { default := TopCat.ofHom ⟨fun _ => default, continuous_const⟩
      uniq := by
        intro f
        apply TopCat.hom_ext
        ext y
        exact Subsingleton.elim _ _ }
  exact IsTerminal.ofUnique _

private noncomputable def realSingZeroIsTerminal :
    IsTerminal
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
        (Δ[0] : SSet.{u})) :=
  realizedZeroIsTerminal.isTerminalObj TopCat.toSSet

private noncomputable def unitObjZeroIso :
    (Δ[0] : SSet.{u}) ≅
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
        (Δ[0] : SSet.{u}) := by
  let _ : IsIso (sSetTopAdj.unit.app (Δ[0] : SSet.{u})) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀
      realSingZeroIsTerminal _
  exact asIso (sSetTopAdj.unit.app (Δ[0] : SSet.{u}))

@[simp]
private theorem unitObjZeroIso_hom :
    unitObjZeroIso.hom =
      sSetTopAdj.unit.app (Δ[0] : SSet.{u}) := rfl

private theorem mono_const_vertex {B : SSet.{u}} (b : B _⦋0⦌) :
    Mono (SSet.const (X := (Δ[0] : SSet.{u})) b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro x y _
  apply SSet.stdSimplex.objEquiv.injective
  subsingleton

private theorem mappedFiberIsPullback (S : FibrationSequence.{u}) :
    IsPullback
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.fiberIncl)
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
        (IsTerminal.from SSet.stdSimplex.isTerminalObj₀ S.fiber))
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.p)
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
        (SSet.const (X := (Δ[0] : SSet.{u})) S.b)) := by
  let _ : Mono (SSet.const (X := (Δ[0] : SSet.{u})) S.b) :=
    mono_const_vertex S.b
  have hTop := (S.fiber_isPullback.flip.map_toTop_of_mono).flip
  exact hTop.map TopCat.toSSet

private theorem adjustedFiberIsPullback (S : FibrationSequence.{u}) :
    IsPullback
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.fiberIncl)
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
          (IsTerminal.from SSet.stdSimplex.isTerminalObj₀ S.fiber) ≫
        unitObjZeroIso.inv)
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.p)
      (SSet.const S.realSingSequence.b) := by
  have h := mappedFiberIsPullback S
  apply h.of_iso (Iso.refl _) (Iso.refl _) unitObjZeroIso.symm
    (Iso.refl _)
  · simp
  · rfl
  · simp
  · change (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
        (SSet.const (X := (Δ[0] : SSet.{u})) S.b) =
      unitObjZeroIso.inv ≫
        SSet.const ((sSetTopAdj.unit.app S.B).app _ S.b)
    apply (cancel_epi unitObjZeroIso.hom).mp
    rw [Iso.hom_inv_id_assoc, unitObjZeroIso_hom]
    rw [← sSetTopAdj.unit.naturality
      (SSet.const (X := (Δ[0] : SSet.{u})) S.b)]
    simp only [Functor.id_map, SSet.const_comp]

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. There is a canonical strict-fiber isomorphism χ:U(F_b)≅fiber(U(p)) over the image
basepoint ηB(b). -/
noncomputable def realSingFiberIso (S : FibrationSequence.{u}) :
    (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.fiber ≅
      S.realSingSequence.fiber := by
  let F : SSet.{u} ⥤ SSet.{u} := SSet.toTop.{u} ⋙ TopCat.toSSet.{u}
  letI : IsIso (sSetTopAdj.unit.app (Δ[0] : SSet.{u})) := by
    rw [← unitObjZeroIso_hom]
    infer_instance
  let e₀ := asIso (sSetTopAdj.unit.app (Δ[0] : SSet.{u}))
  have h : IsPullback
      (F.map S.fiberIncl)
      (F.map (IsTerminal.from SSet.stdSimplex.isTerminalObj₀ S.fiber) ≫ e₀.inv)
      (F.map S.p) (SSet.const S.realSingSequence.b) := by
    have he₀ : e₀ = unitObjZeroIso := by
      apply Iso.ext
      exact unitObjZeroIso_hom.symm
    simpa only [he₀] using adjustedFiberIsPullback S
  exact h.isoIsPullback (F.obj S.E) (Δ[0] : SSet.{u})
    S.realSingSequence.fiber_isPullback

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. The comparison χ commutes with inclusion: χ≫ι_new=U(ι), where ι_new is the strict-fiber
inclusion of the U-image sequence. -/
@[reassoc]
theorem realSingFiberIso_hom_fiberIncl (S : FibrationSequence.{u}) :
    S.realSingFiberIso.hom ≫ S.realSingSequence.fiberIncl =
      (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map S.fiberIncl :=
  (adjustedFiberIsPullback S).isoIsPullback_hom_fst
    ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj S.E)
      (Δ[0] : SSet.{u})
    S.realSingSequence.fiber_isPullback

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. The fiber map of the pointed unit morphism factors as η(F_b)≫χ. -/
@[reassoc]
theorem unitSequenceHom_fiberMap (S : FibrationSequence.{u}) :
    sSetTopAdj.unit.app S.fiber ≫ S.realSingFiberIso.hom =
      S.unitSequenceHom.fiberMap := by
  apply S.realSingSequence.fiber_isPullback.hom_ext
  · rw [Category.assoc, realSingFiberIso_hom_fiberIncl]
    change sSetTopAdj.unit.app S.fiber ≫
        (SSet.toTop ⋙ TopCat.toSSet).map S.fiberIncl =
      S.unitSequenceHom.fiberMap ≫
        S.realSingSequence.fiberIncl
    rw [← sSetTopAdj.unit.naturality S.fiberIncl]
    exact S.unitSequenceHom.fiberMap_ι.symm
  · apply SSet.stdSimplex.isTerminalObj₀.hom_ext

/-- Let p:E→B be a Kan fibration with B Kan, chosen vertices e,b and p(e)=b. Its strict fiber F_b
has the chosen point e and inclusion ι:F_b→E. Put U=Sing∘realization and let η be the adjunction
unit. The composite η(F_b)≫χ sends the chosen original strict-fiber vertex to the chosen
strict-fiber vertex of the U-image sequence. -/
theorem unitSequenceHom_fiberPoint (S : FibrationSequence.{u}) :
    (sSetTopAdj.unit.app S.fiber ≫ S.realSingFiberIso.hom).app _
        S.fiberPoint =
      S.realSingSequence.fiberPoint := by
  rw [unitSequenceHom_fiberMap]
  exact S.unitSequenceHom.fiberMap_app_basePoint

private theorem subsingleton_pi_of_isTerminal
    {T : SSet.{u}} [KanComplex T] (hT : IsTerminal T)
    (t : T _⦋0⦌) (n : ℕ) :
    Subsingleton (KanComplex.π n T t) := by
  constructor
  intro a b
  induction a using KanComplex.π.rec with
  | mk p =>
      induction b using KanComplex.π.rec with
      | mk q =>
          rw [KanComplex.π.mk_eq_mk_iff]
          have hpq : p = q := by
            apply SSet.RelativeMorphism.ext
            exact hT.hom_ext _ _
          subst q
          exact ⟨SSet.PtSimplex.RelStruct₀.refl p⟩

private theorem realSing_basedPath_to_zero_W
    (X : SSet.{u}) (x : X _⦋0⦌) :
    KanComplex.W
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
        (IsTerminal.from SSet.stdSimplex.isTerminalObj₀
        (SSet.basedPath X x))) := by
  let q : SSet.basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    IsTerminal.from SSet.stdSimplex.isTerminalObj₀ _
  let s : (Δ[0] : SSet.{u}) ⟶ SSet.basedPath X x :=
    SSet.const (SSet.basedPathPoint X x)
  have hqs : q ≫ s = SSet.const (SSet.basedPathPoint X x) := by
    simp [q, s]
  let Hleft : SSet.Homotopy (q ≫ s) (𝟙 _) := by
    rw [hqs]
    exact SSet.basedPathContraction X x
  have hsq : s ≫ q = 𝟙 (Δ[0] : SSet.{u}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  let Hright : SSet.Homotopy (s ≫ q) (𝟙 _) := by
    rw [hsq]
    exact SSet.RelativeMorphism.Homotopy.refl _
  let e := SSet.realizedHomotopyEquiv
    (SSet.basedPath X x) (Δ[0] : SSet.{u}) q s Hleft Hright
  have hTop : TopCat.weakHomotopyEquivalences
      (SSet.toTop.map q) := by
    apply TopCat.mem_of_eq_toFun e
    rfl
  exact hTop

private theorem subsingleton_pi_realSing_basedPath
    (X : SSet.{u}) (x : X _⦋0⦌) (n : ℕ) :
    Subsingleton
      (KanComplex.π n
        ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
          (SSet.basedPath X x))
        ((sSetTopAdj.unit.app (SSet.basedPath X x)).app _
          (SSet.basedPathPoint X x))) := by
  let q : SSet.basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    IsTerminal.from SSet.stdSimplex.isTerminalObj₀ _
  have hW : KanComplex.W
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map q) := by
    simpa [q] using realSing_basedPath_to_zero_W X x
  let _ : KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
        (SSet.basedPath X x)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
        (Δ[0] : SSet.{u})) :=
    TopCat.toSSet_obj_kanComplex _
  have hinj := (hW.bijective_piMap n
    ((sSetTopAdj.unit.app (SSet.basedPath X x)).app _
      (SSet.basedPathPoint X x))).1
  constructor
  intro a b
  apply hinj
  exact (subsingleton_pi_of_isTerminal realSingZeroIsTerminal
    (((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map q).app _
      ((sSetTopAdj.unit.app (SSet.basedPath X x)).app _
        (SSet.basedPathPoint X x))) n).elim _ _

/-- For a Kan complex X, vertex x and n∈ℕ, the connecting map of the realization-and-singular image
of its loop fibration sequence is bijective from π(n+1)(Sing(|X|),ηx) to πn of that sequence's
strict fiber at its chosen point. -/
theorem realSingLoop_connectingMap_bijective
    (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) (n : ℕ) :
    Function.Bijective
      ((realSingSequence (SSet.loopFibrationSequence X x)).connectingMap n) := by
  apply connectingMap_bijective_of_subsingleton_total
  intro k
  simpa only [realSingSequence, SSet.loopFibrationSequence] using
    subsingleton_pi_realSing_basedPath X x k

end SSet.FibrationSequence

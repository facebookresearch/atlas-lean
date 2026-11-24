/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHornLeftPositiveIso

/-!
# The zero-right-dimensional left join--horn isomorphism
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace SSet
namespace JoinHorn.Internal

private instance joinHornBoundaryLeftZeroJoinInl_epi (p : ℕ) :
    Epi (joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u})) := by
  rw [← epi_comp_iff_of_isIso _
    ((join.obj (Δ[p + 1] : SSet.{u})).map joinHornBoundaryZeroIso.hom)]
  rw [joinInl_comp_map, joinInl_bot]
  infer_instance


private def joinHornBoundaryLeftZeroFrontIndex (p : ℕ)
    (t : Fin ((((p + 1) + 0 + 1) + 1))) (ht : t.val ≤ p + 1) :
    Fin (p + 2) :=
  ⟨t.val, by omega⟩

private lemma joinHornBoundaryLeftZeroFrontIndex_ne (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1))) (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p 0 i) :
    joinHornBoundaryLeftZeroFrontIndex p t ht ≠ i := by
  intro h
  apply hne
  apply Fin.ext
  have hh := congrArg Fin.val h
  dsimp [joinHornBoundaryLeftZeroFrontIndex, leftJoinHornIndex] at hh ⊢
  exact hh

private noncomputable def joinHornBoundaryLeftZeroFrontFace
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1))) (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p 0 i) :
    (Δ[(p + 1) + 0] : SSet.{u}) ⟶ (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt :=
  joinHornΔcastInv (by omega : p + 0 + 1 = (p + 1) + 0) ≫
    (joinStdSimplexIso p 0).inv ≫
      (join.flip.obj (Δ[0] : SSet.{u})).map
        (horn.ι i (joinHornBoundaryLeftZeroFrontIndex p t ht)
          (joinHornBoundaryLeftZeroFrontIndex_ne p i t ht hne)) ≫
        (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr

private noncomputable def joinHornBoundaryLeftZeroBackFace
    (p : ℕ) (i : Fin (p + 2)) :
    (Δ[(p + 1) + 0] : SSet.{u}) ⟶ (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt :=
  joinHornΔcastInv (by omega : p + 1 = (p + 1) + 0) ≫
    joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
      (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl

private noncomputable def joinHornBoundaryLeftZeroFace
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i) :
    (Δ[(p + 1) + 0] : SSet.{u}) ⟶ (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt :=
  if ht : t.val ≤ p + 1 then
    joinHornBoundaryLeftZeroFrontFace p i t ht hne
  else
    joinHornBoundaryLeftZeroBackFace p i

private lemma joinHornBoundaryLeftZeroFace_front
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i) (ht : t.val ≤ p + 1) :
    joinHornBoundaryLeftZeroFace p i t hne = joinHornBoundaryLeftZeroFrontFace p i t ht hne :=
  dite_eq_left ht

private lemma joinHornBoundaryLeftZeroFace_back
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i) (ht : ¬ t.val ≤ p + 1) :
    joinHornBoundaryLeftZeroFace p i t hne = joinHornBoundaryLeftZeroBackFace p i :=
  dite_eq_right ht


private lemma joinHornBoundaryLeftZeroFrontFace_δ
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1))) (ht : t.val ≤ p + 1)
    (hne : t ≠ leftJoinHornIndex p 0 i)
    (d : Fin (((p + 1) + 0) + 1)) (hd : d.val < p + 2) :
    stdSimplex.δ d ≫ joinHornBoundaryLeftZeroFrontFace p i t ht hne =
      stdSimplex.δ (⟨d.val, hd⟩ : Fin (p + 2)) ≫
        (joinStdSimplexIso p 0).inv ≫
          (join.flip.obj (Δ[0] : SSet.{u})).map
            (horn.ι i (joinHornBoundaryLeftZeroFrontIndex p t ht)
              (joinHornBoundaryLeftZeroFrontIndex_ne p i t ht hne)) ≫
            (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr := by
  unfold joinHornBoundaryLeftZeroFrontFace
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (rfl : p + 1 = p + 1) (rfl : p = p)
      d (⟨d.val, hd⟩ : Fin (p + 2)) rfl,
    joinHornΔcast_rfl, Category.id_comp]

private lemma joinHornBoundaryLeftZeroBackFace_δ
    (p : ℕ) (i : Fin (p + 2))
    (d : Fin (((p + 1) + 0) + 1)) (hd : d.val < p + 2) :
    stdSimplex.δ d ≫ joinHornBoundaryLeftZeroBackFace p i =
      stdSimplex.δ (⟨d.val, hd⟩ : Fin (p + 2)) ≫
        joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
          (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl := by
  unfold joinHornBoundaryLeftZeroBackFace
  rw [joinHornΔcastInv_eq]
  rw [← Category.assoc,
    joinHorn_δ_joinHornΔcast
      (rfl : p + 1 = p + 1) (rfl : p = p)
      d (⟨d.val, hd⟩ : Fin (p + 2)) rfl,
    joinHornΔcast_rfl, Category.id_comp]


set_option maxHeartbeats 500000 in
private lemma joinHornBoundaryLeftZeroFace_compatible
    (p : ℕ) (i : Fin (p + 2)) :
    horn.IsCompatible (joinHornBoundaryLeftZeroFace.{u} p i) := by
  rw [horn.isCompatible_iff]
  intro s t hs ht hst
  by_cases htf : t.val ≤ p + 1
  · have hsf : s.val ≤ p + 1 := by omega
    rw [joinHornBoundaryLeftZeroFace_front p i s hs hsf,
      joinHornBoundaryLeftZeroFace_front p i t ht htf]
    set sr := joinHornBoundaryLeftZeroFrontIndex p s hsf
    set tr := joinHornBoundaryLeftZeroFrontIndex p t htf
    have hsr : sr ≠ i := joinHornBoundaryLeftZeroFrontIndex_ne p i s hsf hs
    have htr : tr ≠ i := joinHornBoundaryLeftZeroFrontIndex_ne p i t htf ht
    have hstr : sr < tr := by
      rw [Fin.lt_def]
      dsimp [sr, tr, joinHornBoundaryLeftZeroFrontIndex]
      exact hst
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < p + 2 := by
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      have := t.isLt
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < p + 2 := by
      have hcast : (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
      omega
    rw [joinHornBoundaryLeftZeroFrontFace_δ p i s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinHornBoundaryLeftZeroFrontFace_δ p i t htf ht
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    obtain _ | p := p
    · have hsrval : sr.val ≠ i.val := fun h => hsr (Fin.ext h)
      have htrval : tr.val ≠ i.val := fun h => htr (Fin.ext h)
      have hstrval : sr.val < tr.val := hstr
      have hsrlt := sr.isLt
      have htrlt := tr.isLt
      have hilt := i.isLt
      omega
    · have haL : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
          Fin ((p + 1) + 2)).val =
          (tr.pred (Fin.ne_zero_of_lt hstr)).val := by
        calc
          (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
          _ = tr.val - 1 := by rfl
          _ = (tr.pred (Fin.ne_zero_of_lt hstr)).val := rfl
      have haR : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
          Fin ((p + 1) + 2)).val =
          (sr.castPred (Fin.ne_last_of_lt hstr)).val := by
        calc
          (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
          _ = sr.val := by rfl
          _ = (sr.castPred (Fin.ne_last_of_lt hstr)).val := rfl
      rw [joinHorn_frontPush_assoc (k' := p) (m := 0)
          (tr.pred (Fin.ne_zero_of_lt hstr))
          (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ : Fin ((p + 1) + 2)) haL,
        joinHorn_frontPush_assoc (k' := p) (m := 0)
          (sr.castPred (Fin.ne_last_of_lt hstr))
          (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ : Fin ((p + 1) + 2)) haR]
      rw [cancel_epi, cancel_epi]
      simp only [← Category.assoc]
      have hc := (horn.IsCompatible.of_hom
        (𝟙 (horn (p + 2) i : SSet.{u}))).δ_pred_comp
          sr tr (hj := hsr) (hk := htr) (hjk := hstr)
      simp only [Category.comp_id] at hc
      have hm := congrArg (join.flip.obj (Δ[0] : SSet.{u})).map hc
      rw [Functor.map_comp, Functor.map_comp] at hm
      exact congrArg (fun z => z ≫
        (joinHornBoundaryLeftPushoutObjObj.{u} (p + 1) 0 i).inr) hm
  · have hsf : s.val ≤ p + 1 := by
      have htlast : t.val = p + 2 := by
        have := t.isLt
        omega
      have hstval : s.val < t.val := hst
      omega
    rw [joinHornBoundaryLeftZeroFace_front p i s hs hsf,
      joinHornBoundaryLeftZeroFace_back p i t ht htf]
    set sr := joinHornBoundaryLeftZeroFrontIndex p s hsf
    have hsr : sr ≠ i := joinHornBoundaryLeftZeroFrontIndex_ne p i s hsf hs
    have htlast : t.val = p + 2 := by
      have := t.isLt
      omega
    have hdL : (t.pred (Fin.ne_zero_of_lt hst)).val < p + 2 := by
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hdR : (s.castPred (Fin.ne_last_of_lt hst)).val < p + 2 := by
      have hcast : (s.castPred (Fin.ne_last_of_lt hst)).val = s.val := rfl
      omega
    rw [joinHornBoundaryLeftZeroFrontFace_δ p i s hsf hs
          (t.pred (Fin.ne_zero_of_lt hst)) hdL,
      joinHornBoundaryLeftZeroBackFace_δ p i
          (s.castPred (Fin.ne_last_of_lt hst)) hdR]
    have hlast : (⟨(t.pred (Fin.ne_zero_of_lt hst)).val, hdL⟩ :
        Fin (p + 2)) = Fin.last (p + 1) := by
      apply Fin.ext
      simp only [Fin.val_last]
      have hp : (t.pred (Fin.ne_zero_of_lt hst)).val = t.val - 1 := rfl
      omega
    have hfront : (⟨(s.castPred (Fin.ne_last_of_lt hst)).val, hdR⟩ :
        Fin (p + 2)) = sr := by
      apply Fin.ext
      dsimp [sr, joinHornBoundaryLeftZeroFrontIndex]
    rw [hlast, joinHorn_backPush_zero_assoc, hfront]
    change (joinInl (Δ[p] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        (join.map (horn.ι i sr hsr)).app (Δ[0] : SSet.{u})) ≫
          (joinHornBoundaryLeftPushoutObjObj p 0 i).inr =
      (stdSimplex.δ sr ≫
        joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u})) ≫
          (joinHornBoundaryLeftPushoutObjObj p 0 i).inl
    calc
      (joinInl (Δ[p] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
          (join.map (horn.ι i sr hsr)).app (Δ[0] : SSet.{u})) ≫
            (joinHornBoundaryLeftPushoutObjObj p 0 i).inr =
        (horn.ι i sr hsr ≫
          joinInl (horn (p + 1) i : SSet.{u}) (Δ[0] : SSet.{u})) ≫
            (joinHornBoundaryLeftPushoutObjObj p 0 i).inr := by
              rw [map_comp_joinInl]
      _ = (horn.ι i sr hsr ≫
          (joinInl (horn (p + 1) i : SSet.{u}) (boundary 0 : SSet.{u}) ≫
            (join.obj (horn (p + 1) i : SSet.{u})).map (boundary 0).ι)) ≫
              (joinHornBoundaryLeftPushoutObjObj p 0 i).inr := by
                rw [joinInl_comp_map]
      _ = (horn.ι i sr hsr ≫
          (joinInl (horn (p + 1) i : SSet.{u}) (boundary 0 : SSet.{u}) ≫
            (join.map (horn (p + 1) i).ι).app (boundary 0 : SSet.{u}))) ≫
              (joinHornBoundaryLeftPushoutObjObj p 0 i).inl := by
                simp only [Category.assoc]
                rw [(joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).isPushout.w]
      _ = ((joinInl (Δ[p] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
          (join.map (horn.ι i sr hsr)).app (boundary 0 : SSet.{u})) ≫
            (join.map (horn (p + 1) i).ι).app (boundary 0 : SSet.{u})) ≫
              (joinHornBoundaryLeftPushoutObjObj p 0 i).inl := by
                slice_lhs 1 2 => rw [map_comp_joinInl]
      _ = (joinInl (Δ[p] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
          (join.map (horn.ι i sr hsr ≫ (horn (p + 1) i).ι)).app
            (boundary 0 : SSet.{u})) ≫
              (joinHornBoundaryLeftPushoutObjObj p 0 i).inl := by
                simp only [Category.assoc, ← NatTrans.comp_app,
                  ← Functor.map_comp]
      _ = (joinInl (Δ[p] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
          (join.map (stdSimplex.δ sr)).app (boundary 0 : SSet.{u})) ≫
            (joinHornBoundaryLeftPushoutObjObj p 0 i).inl := by rw [horn.ι_ι]
      _ = (stdSimplex.δ sr ≫
          joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u})) ≫
            (joinHornBoundaryLeftPushoutObjObj p 0 i).inl := by rw [map_comp_joinInl]


/-- The inverse map obtained from the zero-dimensional face family. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftFromHornZero
    (p : ℕ) (i : Fin (p + 2)) :
    (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i) : SSet.{u}) ⟶
      (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt :=
  (joinHornBoundaryLeftZeroFace_compatible p i).desc

@[reassoc]
private lemma joinHornBoundaryLeftZeroHornFace_fromHorn
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i) :
    horn.ι (leftJoinHornIndex p 0 i) t hne ≫
        joinHornBoundaryLeftFromHornZero p i =
      joinHornBoundaryLeftZeroFace p i t hne :=
  horn.IsCompatible.ι_desc (joinHornBoundaryLeftZeroFace_compatible p i) t hne


private lemma joinHornBoundaryLeftZeroLastIndex_ne
    (p : ℕ) (i : Fin (p + 2)) :
    Fin.last ((p + 1) + 0 + 1) ≠ leftJoinHornIndex p 0 i := by
  intro h
  have hh := congrArg Fin.val h
  dsimp [leftJoinHornIndex] at hh
  have hi := i.isLt
  omega

private lemma joinHornBoundaryLeftJoinInl_zero (p : ℕ) :
    joinInl (Δ[p + 1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫
        (joinStdSimplexIso (p + 1) 0).hom =
      joinHornΔcast (by omega : p + 1 = (p + 1) + 0) ≫
        stdSimplex.δ (Fin.last ((p + 1) + 0 + 1)) := by
  rw [joinHornΔcast_eq _ rfl, joinHornΔcast_rfl, Category.id_comp]
  rw [joinInl_comp_joinStdSimplexIso_hom, inl'_eq_δ_last,
    ← stdSimplex_δ_eq_map]

/-- The boundary-piece map in zero right dimension. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftBoundaryFactorMapZero
    (p : ℕ) (i : Fin (p + 2)) :
    (join.obj (Δ[p + 1] : SSet.{u})).obj (boundary 0 : SSet.{u}) ⟶
      (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i) : SSet.{u}) :=
  (join.obj (Δ[p + 1] : SSet.{u})).map joinHornBoundaryZeroIso.hom ≫
    (joinBotIso (Δ[p + 1] : SSet.{u})).hom ≫
      joinHornΔcast (by omega : p + 1 = (p + 1) + 0) ≫
        horn.ι (leftJoinHornIndex p 0 i) (Fin.last ((p + 1) + 0 + 1))
          (joinHornBoundaryLeftZeroLastIndex_ne p i)

@[reassoc]
lemma joinHornBoundaryLeftBoundaryFactorMapZero_ι
    (p : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftBoundaryFactorMapZero p i ≫
        (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i)).ι =
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary 0).ι ≫
        (joinStdSimplexIso (p + 1) 0).hom := by
  rw [← cancel_epi ((join.obj (Δ[p + 1] : SSet.{u})).map
    joinHornBoundaryZeroIso.inv)]
  unfold joinHornBoundaryLeftBoundaryFactorMapZero
  simp only [Category.assoc]
  rw [horn.ι_ι]
  rw [← (join.obj (Δ[p + 1] : SSet.{u})).map_comp_assoc,
    Iso.inv_hom_id]
  rw [(join.obj (Δ[p + 1] : SSet.{u})).map_id, Category.id_comp]
  change (joinBotIso (Δ[p + 1] : SSet.{u})).hom ≫
      joinHornΔcast _ ≫ stdSimplex.δ (Fin.last ((p + 1) + 0 + 1)) =
    (join.obj (Δ[p + 1] : SSet.{u})).map joinHornBoundaryZeroIso.inv ≫
      (join.obj (Δ[p + 1] : SSet.{u})).map (boundary 0).ι ≫
        (joinStdSimplexIso (p + 1) 0).hom
  have hinit : joinHornBoundaryZeroIso.inv ≫ (boundary 0).ι =
      initial.to (Δ[0] : SSet.{u}) := initialIsInitial.hom_ext _ _
  rw [← (join.obj (Δ[p + 1] : SSet.{u})).map_comp_assoc, hinit]
  rw [← joinHornBoundaryLeftJoinInl_zero p]
  unfold joinInl
  simp only [Category.assoc, Iso.hom_inv_id_assoc]


private instance joinHornBoundaryLeftZeroBackSource_epi (p : ℕ) :
    Epi (joinHornΔcastInv (by omega : p + 1 = (p + 1) + 0) ≫
      joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u})) := by
  rw [joinHornΔcastInv_eq]
  apply epi_comp

private lemma joinHornBoundaryLeftZeroFrontFace_after_iso
    (p : ℕ) (i r : Fin (p + 2)) (hr : r ≠ i) :
    (joinStdSimplexIso p 0).hom ≫
        joinHornBoundaryLeftZeroFace p i (leftJoinHornIndex p 0 r)
          (by
            intro h
            apply hr
            apply Fin.ext
            have hh := congrArg Fin.val h
            simpa only [leftJoinHornIndex] using hh) =
      (join.flip.obj (Δ[0] : SSet.{u})).map (horn.ι i r hr) ≫
        (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr := by
  have ht : (leftJoinHornIndex p 0 r).val ≤ p + 1 := by
    dsimp [leftJoinHornIndex]
    have := r.isLt
    omega
  rw [joinHornBoundaryLeftZeroFace_front p i (leftJoinHornIndex p 0 r) _ ht]
  unfold joinHornBoundaryLeftZeroFrontFace
  rw [joinHornΔcastInv_eq, joinHornΔcast_eq _ rfl, joinHornΔcast_rfl]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  congr 3



private lemma joinHornBoundaryLeftZeroFrontFaceIndex_after_iso
    (p : ℕ) (i r : Fin (p + 2)) (hr : r ≠ i) :
    (joinStdSimplexIso p 0).hom ≫
        joinHornBoundaryLeftZeroFace p i (leftJoinHornIndex p 0 r)
          (leftJoinHornIndex_ne p 0 i r hr) =
      (join.map (horn.ι i r hr)).app (Δ[0] : SSet.{u}) ≫
        (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr := by
  have ht : (leftJoinHornIndex p 0 r).val ≤ p + 1 := by
    dsimp [leftJoinHornIndex]
    have := r.isLt
    omega
  rw [joinHornBoundaryLeftZeroFace_front p i (leftJoinHornIndex p 0 r) _ ht]
  unfold joinHornBoundaryLeftZeroFrontFace
  rw [joinHornΔcastInv_eq, joinHornΔcast_eq _ rfl, joinHornΔcast_rfl]
  simp only [Category.id_comp, Iso.hom_inv_id_assoc]
  congr 3

private lemma joinHornBoundaryLeftZeroFactor_compatible
    (p : ℕ) (i : Fin (p + 2)) :
    (join.map (horn (p + 1) i).ι).app (boundary 0 : SSet.{u}) ≫
        joinHornBoundaryLeftBoundaryFactorMapZero p i =
      (join.obj (horn (p + 1) i : SSet.{u})).map (boundary 0).ι ≫
        joinHornBoundaryLeftHornFactorMap p 0 i := by
  rw [← cancel_mono
    (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i)).ι]
  rw [Category.assoc, joinHornBoundaryLeftBoundaryFactorMapZero_ι,
    Category.assoc, joinHornBoundaryLeftHornFactorMap_ι]
  simp only [← Category.assoc]
  rw [(join.map (horn (p + 1) i).ι).naturality]

/-- The comparison from the zero right-boundary pushout to the shifted horn. -/
@[no_expose]
noncomputable def joinHornBoundaryLeftToHornZero
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt ⟶
      (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i) : SSet.{u}) :=
  (joinHornBoundaryLeftPushoutObjObj p 0 i).isPushout.desc
    (joinHornBoundaryLeftBoundaryFactorMapZero p i)
    (joinHornBoundaryLeftHornFactorMap p 0 i)
    (joinHornBoundaryLeftZeroFactor_compatible p i)

@[reassoc]
lemma joinHornBoundaryLeftPushout_inl_toHornZero
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl ≫ joinHornBoundaryLeftToHornZero p i =
      joinHornBoundaryLeftBoundaryFactorMapZero p i := by
  apply (joinHornBoundaryLeftPushoutObjObj p 0 i).isPushout.inl_desc

@[reassoc]
lemma joinHornBoundaryLeftPushout_inr_toHornZero
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr ≫ joinHornBoundaryLeftToHornZero p i =
      joinHornBoundaryLeftHornFactorMap p 0 i := by
  apply (joinHornBoundaryLeftPushoutObjObj p 0 i).isPushout.inr_desc

@[reassoc]
lemma joinHornBoundaryLeftToHornZero_ι
    (p : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftToHornZero p i ≫
        (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p 0 i).ι ≫
        (joinStdSimplexIso (p + 1) 0).hom := by
  apply (joinHornBoundaryLeftPushoutObjObj p 0 i).hom_ext
  · simp only [← Category.assoc, joinHornBoundaryLeftPushout_inl_toHornZero,
      joinHornBoundaryLeftBoundaryFactorMapZero_ι, (joinHornBoundaryLeftPushoutObjObj p 0 i).inl_ι]
  · simp only [← Category.assoc, joinHornBoundaryLeftPushout_inr_toHornZero,
      joinHornBoundaryLeftHornFactorMap_ι, (joinHornBoundaryLeftPushoutObjObj p 0 i).inr_ι]



private lemma joinHornBoundaryLeftZeroFrontMap_comp
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i)
    (htf : t.val ≤ p + 1) :
    (join.flip.obj (Δ[0] : SSet.{u})).map
        (horn.ι i (joinHornBoundaryLeftZeroFrontIndex p t htf)
          (joinHornBoundaryLeftZeroFrontIndex_ne p i t htf hne)) ≫
      (join.map (horn (p + 1) i).ι).app (Δ[0] : SSet.{u}) =
    (join.map (stdSimplex.δ (joinHornBoundaryLeftZeroFrontIndex p t htf))).app
      (Δ[0] : SSet.{u}) := by
  change (join.map
      (horn.ι i (joinHornBoundaryLeftZeroFrontIndex p t htf)
        (joinHornBoundaryLeftZeroFrontIndex_ne p i t htf hne))).app
        (Δ[0] : SSet.{u}) ≫
      (join.map (horn (p + 1) i).ι).app (Δ[0] : SSet.{u}) = _
  rw [← NatTrans.comp_app, ← Functor.map_comp, horn.ι_ι]

@[reassoc]
private lemma joinHornBoundaryLeftZeroFace_toHorn
    (p : ℕ) (i : Fin (p + 2))
    (t : Fin ((((p + 1) + 0 + 1) + 1)))
    (hne : t ≠ leftJoinHornIndex p 0 i) :
    joinHornBoundaryLeftZeroFace p i t hne ≫ joinHornBoundaryLeftToHornZero p i =
      horn.ι (leftJoinHornIndex p 0 i) t hne := by
  rw [← cancel_mono
    (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i)).ι]
  simp only [Category.assoc, joinHornBoundaryLeftToHornZero_ι, horn.ι_ι]
  by_cases htf : t.val ≤ p + 1
  · rw [joinHornBoundaryLeftZeroFace_front p i t hne htf]
    unfold joinHornBoundaryLeftZeroFrontFace
    simp only [Category.assoc]
    rw [(joinHornBoundaryLeftPushoutObjObj p 0 i).inr_ι_assoc]
    slice_lhs 3 4 => rw [joinHornBoundaryLeftZeroFrontMap_comp p i t hne htf]
    let r := joinHornBoundaryLeftZeroFrontIndex p t htf
    have hrval : r.val = t.val := rfl
    have hdual := joinHorn_dualFrontPush (k' := p) (m := 0)
      r t hrval.symm (by omega : p + 0 + 1 = (p + 1) + 0)
    rw [hdual]
    slice_lhs 2 3 => rw [Iso.inv_hom_id]
    rw [Category.id_comp]
    rw [joinHornΔcastInv_eq]
    slice_lhs 1 2 => rw [joinHornΔcast_comp_eq_id]
    rw [Category.id_comp]
  · rw [joinHornBoundaryLeftZeroFace_back p i t hne htf]
    unfold joinHornBoundaryLeftZeroBackFace
    simp only [Category.assoc]
    rw [(joinHornBoundaryLeftPushoutObjObj p 0 i).inl_ι_assoc]
    slice_lhs 2 3 => rw [joinInl_comp_map]
    rw [joinHornBoundaryLeftJoinInl_zero]
    rw [joinHornΔcastInv_eq]
    slice_lhs 1 2 => rw [joinHornΔcast_comp_eq_id]
    rw [Category.id_comp]
    congr 1
    apply Fin.ext
    simp only [Fin.val_last]
    have := t.isLt
    omega


lemma joinHornBoundaryLeftFromHornZero_toHorn
    (p : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftFromHornZero p i ≫ joinHornBoundaryLeftToHornZero p i =
      𝟙 (horn ((p + 1) + 0 + 1)
        (leftJoinHornIndex p 0 i) : SSet.{u}) := by
  apply horn.hom_ext'
  intro t hne
  rw [joinHornBoundaryLeftZeroHornFace_fromHorn_assoc,
    joinHornBoundaryLeftZeroFace_toHorn, Category.comp_id]

set_option maxHeartbeats 1000000 in
lemma joinHornBoundaryLeftToHornZero_fromHorn
    (p : ℕ) (i : Fin (p + 2)) :
    joinHornBoundaryLeftToHornZero p i ≫ joinHornBoundaryLeftFromHornZero p i =
      𝟙 (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt := by
  apply (joinHornBoundaryLeftPushoutObjObj p 0 i).hom_ext
  · simp only [Category.comp_id]
    let src : (Δ[(p + 1) + 0] : SSet.{u}) ⟶
        (join.obj (Δ[p + 1] : SSet.{u})).obj (boundary 0 : SSet.{u}) :=
      joinHornΔcastInv (by omega : p + 1 = (p + 1) + 0) ≫
        joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u})
    let _ : Epi src := joinHornBoundaryLeftZeroBackSource_epi p
    rw [← cancel_epi src]
    let z : Fin (((p + 1) + 0 + 1) + 1) := Fin.last ((p + 1) + 0 + 1)
    have hz : z ≠ leftJoinHornIndex p 0 i := joinHornBoundaryLeftZeroLastIndex_ne p i
    have hback : ¬ z.val ≤ p + 1 := by
      dsimp [z]
      omega
    have hface : joinHornBoundaryLeftZeroFace p i z hz =
        src ≫ (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl := by
      rw [joinHornBoundaryLeftZeroFace_back p i z hz hback]
      rfl
    dsimp only [src] at hface
    have hface' : joinHornBoundaryLeftZeroFace p i z hz =
        joinHornΔcastInv (by omega : p + 1 = (p + 1) + 0) ≫
          joinInl (Δ[p + 1] : SSet.{u}) (boundary 0 : SSet.{u}) ≫
            (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl := by
      simpa only [Category.assoc] using hface
    slice_lhs 1 3 => rw [← hface']
    slice_lhs 1 2 => rw [joinHornBoundaryLeftZeroFace_toHorn]
    rw [joinHornBoundaryLeftZeroHornFace_fromHorn, hface']
    dsimp only [src]
    simp only [Category.assoc]
  · simp only [Category.comp_id]
    apply joinHornBoundaryLeftHorn_hom_ext p 0 i
    intro r hr
    slice_lhs 2 3 => rw [joinHornBoundaryLeftPushout_inr_toHornZero]
    slice_lhs 1 2 => rw [joinHornBoundaryLeftHornFactorMap_face]
    rw [joinHornΔcast_eq _ rfl, joinHornΔcast_rfl, Category.id_comp]
    slice_lhs 2 3 => rw [joinHornBoundaryLeftZeroHornFace_fromHorn]
    rw [joinHornBoundaryLeftZeroFrontFaceIndex_after_iso]

/-- The left horn--boundary point isomorphism in zero right dimension. -/
noncomputable def joinHornBoundaryLeftPointIsoZero
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).pt ≅
      (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i) : SSet.{u}) where
  hom := joinHornBoundaryLeftToHornZero p i
  inv := joinHornBoundaryLeftFromHornZero p i
  hom_inv_id := joinHornBoundaryLeftToHornZero_fromHorn p i
  inv_hom_id := joinHornBoundaryLeftFromHornZero_toHorn p i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoZero_hom_ι
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPointIsoZero.{u} p i).hom ≫
        (horn ((p + 1) + 0 + 1) (leftJoinHornIndex p 0 i)).ι =
      (joinHornBoundaryLeftPushoutObjObj p 0 i).ι ≫ (joinStdSimplexIso (p + 1) 0).hom :=
  joinHornBoundaryLeftToHornZero_ι p i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoZero_hom_inl
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inl ≫ (joinHornBoundaryLeftPointIsoZero p i).hom =
      joinHornBoundaryLeftBoundaryFactorMapZero p i :=
  joinHornBoundaryLeftPushout_inl_toHornZero p i

@[reassoc]
lemma joinHornBoundaryLeftPointIsoZero_hom_inr
    (p : ℕ) (i : Fin (p + 2)) :
    (joinHornBoundaryLeftPushoutObjObj.{u} p 0 i).inr ≫ (joinHornBoundaryLeftPointIsoZero p i).hom =
      joinHornBoundaryLeftHornFactorMap p 0 i :=
  joinHornBoundaryLeftPushout_inr_toHornZero p i

end JoinHorn.Internal
end SSet

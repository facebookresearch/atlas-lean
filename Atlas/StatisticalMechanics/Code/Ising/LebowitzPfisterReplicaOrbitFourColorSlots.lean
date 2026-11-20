/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor











open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaFourColorSlotsDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


def lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4) :
    ↑(Finset.univ : Finset β) -> Fin 4 :=
  fun x => color ⟨E.symm x.1, Finset.mem_univ _⟩


theorem colorClass_lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (a : Fin 4) :
    colorClass Finset.univ (lpReplicaFourColorTransport E color) a =
      (colorClass Finset.univ color a).map E.toEmbedding := by
  ext x
  simp [colorClass, lpReplicaFourColorTransport]


theorem rowClass_lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (r : Fin 2) :
    rowClass Finset.univ (lpReplicaFourColorTransport E color) r =
      (rowClass Finset.univ color r).map E.toEmbedding := by
  by_cases hr : r = 0
  · subst r
    rw [rowClass_zero, rowClass_zero,
      colorClass_lpReplicaFourColorTransport,
      colorClass_lpReplicaFourColorTransport, Finset.map_union]
  · have hr1 : r = 1 := by omega
    subst r
    rw [rowClass_one, rowClass_one,
      colorClass_lpReplicaFourColorTransport,
      colorClass_lpReplicaFourColorTransport, Finset.map_union]



theorem leftPattern_lpReplicaFourColorTransport
    {α β W : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype W] [DecidableEq W]
    (E : α ≃ β) (endsα : α -> Sym2 W) (endsβ : β -> Sym2 W)
    (hends : forall x, endsβ (E x) = endsα x)
    (A B : Finset W) (u v : W)
    (color : ↑(Finset.univ : Finset α) -> Fin 4)
    (hleft : LeftPattern endsα Finset.univ A B u v color) :
    LeftPattern endsβ Finset.univ A B u v
      (lpReplicaFourColorTransport E color) := by
  rcases hleft with ⟨h0, h1, h2, h3, hd0, hd1⟩
  unfold LeftPattern RowsDisconnect
  rw [colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    colorClass_lpReplicaFourColorTransport,
    rowClass_lpReplicaFourColorTransport,
    rowClass_lpReplicaFourColorTransport]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h0
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h1
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h2
  · rw [randomCurrent_sources_map_embedding
      endsα endsβ E.toEmbedding hends]
    exact h3
  · intro huv
    exact hd0 ((randomCurrent_connK_map_embedding
      endsα endsβ E.toEmbedding hends _ u v).1 huv)
  · intro huv
    exact hd1 ((randomCurrent_connK_map_embedding
      endsα endsβ E.toEmbedding hends _ u v).1 huv)



theorem lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    (hfixed : e ∉ lpReplicaCurrentEdgeOrbitFixed G sites)
    (hstrict : e ∉ lpReplicaCurrentEdgeOrbitStrictReps G sites) :
    lpReplicaCurrentEdgeReflect G sites e ∈
      lpReplicaCurrentEdgeOrbitStrictReps G sites := by
  have hne : e ≠ lpReplicaCurrentEdgeReflect G sites e := by
    intro he
    exact hfixed ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e).2 he)
  have hreflectRep : lpReplicaCurrentEdgeReflect G sites e ∈
      lpReplicaCurrentEdgeOrbitReps G sites := by
    rcases lpReplicaCurrentEdge_mem_reps_or_reflect_mem_reps
        G sites e with heRep | hreflectRep
    · exact False.elim (hstrict
        ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e).2
          ⟨heRep, hne⟩))
    · exact hreflectRep
  rw [mem_lpReplicaCurrentEdgeOrbitStrictReps]
  refine ⟨hreflectRep, ?_⟩
  intro he
  apply hne
  change lpReplicaCurrentEdgeReflect G sites e =
    lpReplicaCurrentEdgeReflect G sites
      (lpReplicaCurrentEdgeReflect G sites e) at he
  exact (lpReplicaCurrentEdgeReflect G sites).injective he



noncomputable def lpReplicaCurrentEdgeOrbitCoordEquiv
    (G : SimpleGraph V) (sites : I -> V) :
    (lpReplicaCurrentGraph G sites).edgeFinset ≃
      ↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
        (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
          ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) where
  toFun e := by
    classical
    by_cases hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites
    · exact Sum.inl ⟨e, hfixed⟩
    · by_cases hstrict : e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites
      · exact Sum.inr (Sum.inl ⟨e, hstrict⟩)
      · exact Sum.inr (Sum.inr
          ⟨lpReplicaCurrentEdgeReflect G sites e,
            lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem
              G sites e hfixed hstrict⟩)
  invFun
    | Sum.inl e => e.1
    | Sum.inr (Sum.inl e) => e.1
    | Sum.inr (Sum.inr e) => lpReplicaCurrentEdgeReflect G sites e.1
  left_inv := by
    classical
    intro e
    by_cases hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites
    · simp [hfixed]
    · by_cases hstrict : e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites
      · simp [hfixed, hstrict]
      · simp only [hfixed, hstrict, ↓reduceDIte]
        exact lpReplicaCurrentEdgeReflect_involutive G sites e
  right_inv := by
    classical
    intro x
    rcases x with fixed | strict
    · simp [fixed.2]
    · rcases strict with rep | reflected
      · have hnotFixed : rep.1 ∉
            lpReplicaCurrentEdgeOrbitFixed G sites := by
          intro hfixed
          exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites rep.1).1
            rep.2).2 ((mem_lpReplicaCurrentEdgeOrbitFixed G sites rep.1).1
              hfixed)
        simp [hnotFixed, rep.2]
      · have hnotFixed : lpReplicaCurrentEdgeReflect G sites reflected.1 ∉
            lpReplicaCurrentEdgeOrbitFixed G sites := by
          intro hfixed
          have heq := (mem_lpReplicaCurrentEdgeOrbitFixed G sites _).1 hfixed
          have heq' : lpReplicaCurrentEdgeReflect G sites reflected.1 =
              reflected.1 := by
            rw [lpReplicaCurrentEdgeReflect_involutive] at heq
            exact heq
          exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites reflected.1).1
            reflected.2).2 heq'.symm
        have hnotStrict : lpReplicaCurrentEdgeReflect G sites reflected.1 ∉
            lpReplicaCurrentEdgeOrbitStrictReps G sites := by
          intro hstrict
          have hrep := (mem_lpReplicaCurrentEdgeOrbitStrictReps
            G sites reflected.1).1 reflected.2
          have href := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites
            (lpReplicaCurrentEdgeReflect G sites reflected.1)).1 hstrict
          exact hrep.2
            (lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
              G sites reflected.1 hrep.1 (by
                simpa only [lpReplicaCurrentEdgeReflect_involutive]
                  using href.1))
        simp only [hnotFixed, hnotStrict, ↓reduceDIte]
        apply congrArg Sum.inr
        apply congrArg Sum.inr
        apply Subtype.ext
        exact lpReplicaCurrentEdgeReflect_involutive G sites reflected.1

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (Sum.inl e) = e.1 := rfl

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (Sum.inr (Sum.inl e)) = e.1 := rfl

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (Sum.inr (Sum.inr e)) =
      lpReplicaCurrentEdgeReflect G sites e.1 := rfl



theorem lpReplicaProfile_eq_half_of_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)) :
    m e.1 = q e.1 / 2 := by
  have heq := congrFun hm e.1
  have hreflect := (mem_lpReplicaCurrentEdgeOrbitFixed G sites e.1).1 e.2
  unfold lpReplicaSymmetrizedProfile at heq
  have hmreflect : m (lpReplicaCurrentEdgeReflect G sites e.1) = m e.1 :=
    congrArg m hreflect.symm
  have : m e.1 + m e.1 = q e.1 := by simpa only [hmreflect] using heq
  omega



theorem lpReplicaProfile_eq_of_orbitLabel_allocation_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n)
    (halloc : (fun e => (L e).1) = fun e => (M e).1) :
    m = n := by
  funext e
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  generalize hcoord : E e = coord
  rcases coord with fixed | strict
  · have he : e = fixed.1 := by
      calc
        e = E.symm (E e) := (E.symm_apply_apply e).symm
        _ = fixed.1 := by
          simpa only [E,
            lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed] using
              congrArg E.symm hcoord
    subst e
    rw [lpReplicaProfile_eq_half_of_fixed G sites q m hm fixed,
      lpReplicaProfile_eq_half_of_fixed G sites q n hn fixed]
  · rcases strict with rep | reflected
    · have he : e = rep.1 := by
        calc
          e = E.symm (E e) := (E.symm_apply_apply e).symm
          _ = rep.1 := by
            simpa only [E,
              lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict] using
                congrArg E.symm hcoord
      subst e
      have hLM := congrFun halloc rep
      have hLcard := (Finset.mem_powersetCard.mp (L rep).2).2
      have hMcard := (Finset.mem_powersetCard.mp (M rep).2).2
      rw [← hLcard, ← hMcard, hLM]
    · have he : e = lpReplicaCurrentEdgeReflect G sites reflected.1 := by
        calc
          e = E.symm (E e) := (E.symm_apply_apply e).symm
          _ = lpReplicaCurrentEdgeReflect G sites reflected.1 := by
            simpa only [E,
              lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict] using
                congrArg E.symm hcoord
      subst e
      have hLM := congrFun halloc reflected
      have hLcard := (Finset.mem_powersetCard.mp (L reflected).2).2
      have hMcard := (Finset.mem_powersetCard.mp (M reflected).2).2
      have hrep : m reflected.1 = n reflected.1 := by
        rw [← hLcard, ← hMcard, hLM]
      have hqm := congrFun hm reflected.1
      have hqn := congrFun hn reflected.1
      unfold lpReplicaSymmetrizedProfile at hqm hqn
      omega



noncomputable def lpReplicaProfileOrbitPairedCoordEquivSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    Fin (m e.1) ⊕
        Fin (m (lpReplicaCurrentEdgeReflect G sites e.1)) ≃
      Fin (q e.1) := by
  classical
  have hleft : (L e).1.card = m e.1 :=
    (Finset.mem_powersetCard.mp (L e).2).2
  have hright : (Finset.univ \ (L e).1).card =
      m (lpReplicaCurrentEdgeReflect G sites e.1) := by
    have hq := congrFun hm e.1
    unfold lpReplicaSymmetrizedProfile at hq
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hleft]
    omega
  let left : Fin (m e.1) ≃ {x : Fin (q e.1) // x ∈ (L e).1} :=
    (L e).1.orderIsoOfFin hleft
  let right0 : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1)) ≃
      {x : Fin (q e.1) // x ∈ Finset.univ \ (L e).1} :=
    (Finset.univ \ (L e).1).orderIsoOfFin hright
  let rightCast : {x : Fin (q e.1) // x ∈ Finset.univ \ (L e).1} ≃
      {x : Fin (q e.1) // x ∉ (L e).1} := {
    toFun x := ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
    invFun x := ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  exact (Equiv.sumCongr left (right0.trans rightCast)).trans
    (Equiv.sumCompl fun x : Fin (q e.1) => x ∈ (L e).1)

@[simp] theorem lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
        (Sum.inl k) ∈ (L e).1 := by
  classical
  simp [lpReplicaProfileOrbitPairedCoordEquivSlot]

@[simp] theorem lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
        (Sum.inr k) ∉ (L e).1 := by
  classical
  have hleft : (L e).1.card = m e.1 :=
    (Finset.mem_powersetCard.mp (L e).2).2
  have hright : (Finset.univ \ (L e).1).card =
      m (lpReplicaCurrentEdgeReflect G sites e.1) := by
    have hq := congrFun hm e.1
    unfold lpReplicaSymmetrizedProfile at hq
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hleft]
    omega
  change (((Finset.univ \ (L e).1).orderIsoOfFin hright) k).1 ∉ (L e).1
  exact (Finset.mem_sdiff.mp
    (((Finset.univ \ (L e).1).orderIsoOfFin hright) k).2).2



def LPReplicaOrbitProfileCopyCoord
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ c : ↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
      (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)),
    Fin (m ((lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm c))


noncomputable def lpReplicaProfileCopyEquivOrbitCoord
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      LPReplicaOrbitProfileCopyCoord G sites m :=
  Equiv.sigmaCongr (lpReplicaCurrentEdgeOrbitCoordEquiv G sites) fun e =>
    Equiv.cast (congrArg Fin (congrArg m
      ((lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm_apply_apply e).symm))


@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_fst
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 =
      lpReplicaCurrentEdgeOrbitCoordEquiv G sites c.1 := by
  rfl



@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_snd_val
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaProfileCopyEquivOrbitCoord G sites m c).2.1 = c.2.1 := by
  rcases c with ⟨e, k⟩
  have castVal (a b : Nat) (h : a = b) (x : Fin a) :
      (Equiv.cast (congrArg Fin h) x).1 = x.1 := by
    subst b
    rfl
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  change (Equiv.cast (congrArg Fin
    (congrArg m (E.symm_apply_apply e).symm)) k).1 = k.1
  exact castVal _ _ (congrArg m (E.symm_apply_apply e).symm) k



@[simp] theorem lpReplicaProfileCopyEquivOrbitCoord_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 = c.1 := by
  exact (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm_apply_apply c.1




def LPReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  (Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), Fin (q e.1 / 2)) ⊕
    (Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Fin (q e.1))

noncomputable instance instFintypeLPReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaOrbitCommonSlot G sites q) := by
  unfold LPReplicaOrbitCommonSlot
  infer_instance

noncomputable instance instDecidableEqLPReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    DecidableEq (LPReplicaOrbitCommonSlot G sites q) :=
  Classical.decEq _



theorem card_lpReplicaOrbitCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrbitCommonSlot G sites q) =
      (∑ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), q e.1 / 2) +
        ∑ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), q e.1 := by
  unfold LPReplicaOrbitCommonSlot
  calc
    _ = Fintype.card
          (Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), Fin (q e.1 / 2)) +
        Fintype.card
          (Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Fin (q e.1)) :=
      Fintype.card_sum
    _ = _ := by
      rw [Fintype.card_sigma, Fintype.card_sigma]
      simp




noncomputable def lpReplicaOrbitProfileCoordEquivCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaOrbitProfileCopyCoord G sites m ≃
      LPReplicaOrbitCommonSlot G sites q := by
  classical
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  let F : (↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
      (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))) -> Type :=
    fun c => Fin (m (E.symm c))
  let outer := Equiv.sumSigmaDistrib F
  let inner := Equiv.sumSigmaDistrib
    (fun c : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) => F (Sum.inr c))
  let distribute := outer.trans (Equiv.sumCongr (Equiv.refl _) inner)
  let FixedCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites),
    F (Sum.inl e)
  let LeftCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inl e))
  let RightCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inr e))
  let PairedCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inl e)) ⊕ F (Sum.inr (Sum.inr e))
  let FixedSlot := Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites),
    Fin (q e.1 / 2)
  let StrictSlot := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    Fin (q e.1)
  let regroup : FixedCoord ⊕ (LeftCoord ⊕ RightCoord) ≃
      FixedCoord ⊕ PairedCoord := Equiv.sumCongr (Equiv.refl FixedCoord)
    (Equiv.sigmaSumDistrib
      (fun e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
        F (Sum.inr (Sum.inl e)))
      (fun e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
        F (Sum.inr (Sum.inr e)))).symm
  let fixedSlots : FixedCoord ≃ FixedSlot :=
    Equiv.sigmaCongrRight fun e :
      ↑(lpReplicaCurrentEdgeOrbitFixed G sites) =>
    Equiv.cast (congrArg Fin
      (lpReplicaProfile_eq_half_of_fixed G sites q m hm e))
  let pairedSlots : PairedCoord ≃ StrictSlot :=
    Equiv.sigmaCongrRight fun e :
      ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
  exact distribute.trans regroup |>.trans
    (Equiv.sumCongr fixedSlots pairedSlots)



noncomputable def lpReplicaProfileCopyEquivCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      LPReplicaOrbitCommonSlot G sites q :=
  (lpReplicaProfileCopyEquivOrbitCoord G sites m).trans
    (lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L)

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites))
    (k : Fin (m e.1)) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inl e, k⟩ =
      Sum.inl ⟨e, Equiv.cast (congrArg Fin
        (lpReplicaProfile_eq_half_of_fixed G sites q m hm e)) k⟩ := by
  rfl

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inr (Sum.inl e), k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
          (Sum.inl k)⟩ := by
  rfl

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inr (Sum.inr e), k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
          (Sum.inr k)⟩ := by
  rfl



@[simp] theorem lpReplicaProfileCopyEquivCommonSlot_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaProfileCopyEquivCommonSlot G sites q m hm L ⟨e.1, k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitLabelRepEmbedding G sites q m L e k⟩ := by
  classical
  have hnotFixed : e.1 ∉ lpReplicaCurrentEdgeOrbitFixed G sites := by
    intro hfixed
    exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2).2
      ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e.1).1 hfixed)
  let d := lpReplicaProfileCopyEquivOrbitCoord G sites m ⟨e.1, k⟩
  have hdFst : d.1 = Sum.inr (Sum.inl e) := by
    dsimp only [d]
    rw [lpReplicaProfileCopyEquivOrbitCoord_fst]
    apply (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm.injective
    simp
  have hdVal : d.2.1 = k.1 := by
    simpa only [d] using
      lpReplicaProfileCopyEquivOrbitCoord_snd_val G sites m ⟨e.1, k⟩
  change lpReplicaOrbitProfileCoordEquivCommonSlot
      G sites q m hm L d = _
  rcases d with ⟨de, dk⟩
  dsimp only at hdFst hdVal
  subst de
  have hdk : dk = k := Fin.ext hdVal
  subst dk
  rw [lpReplicaOrbitProfileCoordEquivCommonSlot_strict]
  rfl



@[simp] theorem lpReplicaProfileCopyEquivCommonSlot_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
        ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitLabelReflectEmbedding
          G sites q m hm L e k⟩ := by
  classical
  have hnotFixed : lpReplicaCurrentEdgeReflect G sites e.1 ∉
      lpReplicaCurrentEdgeOrbitFixed G sites := by
    intro hfixed
    have heq := (mem_lpReplicaCurrentEdgeOrbitFixed G sites _).1 hfixed
    have heq' : lpReplicaCurrentEdgeReflect G sites e.1 = e.1 := by
      rw [lpReplicaCurrentEdgeReflect_involutive] at heq
      exact heq
    exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2).2
      heq'.symm
  have hnotStrict : lpReplicaCurrentEdgeReflect G sites e.1 ∉
      lpReplicaCurrentEdgeOrbitStrictReps G sites := by
    intro hstrict
    have hrep := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2
    have href := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites
      (lpReplicaCurrentEdgeReflect G sites e.1)).1 hstrict
    exact hrep.2
      (lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
        G sites e.1 hrep.1 (by
          simpa only [lpReplicaCurrentEdgeReflect_involutive] using href.1))
  let d := lpReplicaProfileCopyEquivOrbitCoord G sites m
    ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩
  have hdFst : d.1 = Sum.inr (Sum.inr e) := by
    dsimp only [d]
    rw [lpReplicaProfileCopyEquivOrbitCoord_fst]
    apply (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm.injective
    simp
  have hdVal : d.2.1 = k.1 := by
    simpa only [d] using
      lpReplicaProfileCopyEquivOrbitCoord_snd_val G sites m
        ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩
  change lpReplicaOrbitProfileCoordEquivCommonSlot
      G sites q m hm L d = _
  rcases d with ⟨de, dk⟩
  dsimp only at hdFst hdVal
  subst de
  have hdk : dk = k := Fin.ext hdVal
  subst dk
  rw [lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict]
  rfl



structure LPReplicaOrbitFourColorSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  allocation : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    Finset (Fin (q e.1))
  color : ↑(Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)) -> Fin 4



noncomputable def lpReplicaOrbitFourColorSlotStateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := fun e => (L e).1
  color := fun x => lpReplicaRowTagEquivFin4
    (tag ((lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).symm x.1))

@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).allocation =
      fun e => (L e).1 := rfl


@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_color_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c,
          Finset.mem_univ _⟩ =
      lpReplicaRowTagEquivFin4 (tag c) := by
  simp [lpReplicaOrbitFourColorSlotStateOfTag]

@[ext]
theorem LPReplicaOrbitFourColorSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {s t : LPReplicaOrbitFourColorSlotState G sites q}
    (ha : s.allocation = t.allocation) (hc : s.color = t.color) : s = t := by
  cases s
  cases t
  cases ha
  cases hc
  rfl



theorem lpReplicaOrbitFourColorSlotStateOfTag_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    Function.Injective
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L) := by
  intro tag₁ tag₂ hstate
  funext c
  have hcolor := congrArg
    (fun s : LPReplicaOrbitFourColorSlotState G sites q => s.color
      ⟨lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c,
        Finset.mem_univ _⟩) hstate
  simp only [lpReplicaOrbitFourColorSlotStateOfTag_color_copy] at hcolor
  exact lpReplicaRowTagEquivFin4.injective hcolor



def lpReplicaRowToggleFin4 (a : Fin 4) : Fin 4 :=
  let tag := lpReplicaRowTagEquivFin4.symm a
  lpReplicaRowTagEquivFin4 (!tag.1, tag.2)


theorem lpReplicaRowToggleFin4_involutive :
    Function.Involutive lpReplicaRowToggleFin4 := by
  intro a
  fin_cases a <;> rfl

@[simp] theorem lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst
    (a : Fin 4) :
    (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).1 =
      !(lpReplicaRowTagEquivFin4.symm a).1 := by
  fin_cases a <;> rfl



def lpReplicaOrbitFourColorSlotRowToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := s.allocation
  color := fun x => if x.1 ∈ P then lpReplicaRowToggleFin4 (s.color x)
    else s.color x


theorem lpReplicaOrbitFourColorSlotRowToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotRowToggle G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · funext x
    change (if x.1 ∈ P then
        lpReplicaRowToggleFin4
          (if x.1 ∈ P then lpReplicaRowToggleFin4 (s.color x)
            else s.color x)
      else if x.1 ∈ P then lpReplicaRowToggleFin4 (s.color x)
        else s.color x) = s.color x
    by_cases hx : x.1 ∈ P
    · rw [if_pos hx, if_pos hx]
      exact lpReplicaRowToggleFin4_involutive (s.color x)
    · rw [if_neg hx, if_neg hx]




noncomputable def lpReplicaOrbitCommonSlotsOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    Finset (LPReplicaOrbitCommonSlot G sites q) :=
  P.map (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).toEmbedding



theorem mem_lpReplicaOrbitCommonSlotsOfCopies_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaOrbitCommonSlot G sites q) :
    x ∈ lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P ↔
      (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).symm x ∈ P := by
  classical
  simp [lpReplicaOrbitCommonSlotsOfCopies]


theorem lpReplicaOrbitFourColorSlotRowToggle_stateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotRowToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L
        (lpReplicaToggleRows G sites m P tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · funext x
    let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let c := E.symm x.1
    have hx : x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
        G sites q m hm L P ↔ c ∈ P := by
      exact mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x.1
    change (if x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
          G sites q m hm L P then
        lpReplicaRowToggleFin4
          (lpReplicaRowTagEquivFin4 (tag c))
      else lpReplicaRowTagEquivFin4 (tag c)) =
      lpReplicaRowTagEquivFin4
        (if c ∈ P then (!(tag c).1, (tag c).2) else tag c)
    by_cases hc : c ∈ P
    · rw [if_pos (hx.mpr hc), if_pos hc]
      rcases htag : tag c with ⟨row, current⟩
      cases row <;> cases current <;> rfl
    · rw [if_neg (fun h => hc (hx.mp h)), if_neg hc]



def lpReplicaOrbitFourColorSlotEdge
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitCommonSlot G sites q ->
      (lpReplicaCurrentGraph G sites).edgeFinset
  | Sum.inl fixed => fixed.1.1
  | Sum.inr strict =>
      if strict.2 ∈ s.allocation strict.1 then strict.1.1
      else lpReplicaCurrentEdgeReflect G sites strict.1.1



theorem lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
        (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) = c.1 := by
  classical
  let C := lpReplicaProfileCopyEquivOrbitCoord G sites m
  let Q := lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
  let d := C c
  have hedge : (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm d.1 = c.1 :=
    lpReplicaProfileCopyEquivOrbitCoord_edge G sites m c
  change lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
      (Q d) = c.1
  rcases d with ⟨fixed | strict, k⟩
  · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_fixed]
    change fixed.1 = c.1
    simpa using hedge
  · rcases strict with rep | reflected
    · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_strict]
      rw [lpReplicaOrbitFourColorSlotEdge]
      simp only [lpReplicaOrbitFourColorSlotStateOfTag_allocation,
        lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem, ↓reduceIte]
      simpa using hedge
    · rw [lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict]
      rw [lpReplicaOrbitFourColorSlotEdge]
      simp only [lpReplicaOrbitFourColorSlotStateOfTag_allocation,
        lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem,
        ↓reduceIte]
      simpa using hedge


def lpReplicaOrbitFourColorSlotEnds
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitCommonSlot G sites q -> Sym2 (LPReplicaCurrentVertex V) :=
  fun x => (lpReplicaOrbitFourColorSlotEdge G sites q s x).1



theorem lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
        (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) =
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m c := by
  unfold lpReplicaOrbitFourColorSlotEnds
  unfold StatMech.Sharpness.FluxEdgeCopy.endsM
  rw [lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy]



def lpReplicaOrbitFourColorSlotRecolor
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (X Y : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := s.allocation
  color := balancedSwap Finset.univ X Y s.color


def lpReplicaOrbitFourColorSelectedStrictSlots
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    Finset (Fin (q e.1)) :=
  Finset.univ.filter fun k =>
    (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P



theorem lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    lpReplicaOrbitFourColorSelectedStrictSlots G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) e =
      ((lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L).2 e).1.1 ∪
        ((lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L).2 e).2.1 := by
  classical
  ext k
  simp only [lpReplicaOrbitFourColorSelectedStrictSlots,
    Finset.mem_filter, Finset.mem_univ, true_and,
    lpReplicaProfileOrbitSelectedLabelOfCopies,
    lpReplicaCopyIndicesAtEdge, Finset.mem_union, Finset.mem_map]
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let x : LPReplicaOrbitCommonSlot G sites q := Sum.inr ⟨e, k⟩
  constructor
  · intro hx
    have hc : E.symm x ∈ P :=
      (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mp hx
    let c := E.symm x
    change c ∈ P at hc
    have hEc : E c = x := E.apply_symm_apply x
    let tag : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
      fun _ => (false, false)
    have hedgeCopy := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
      G sites q m hm L tag c
    have hedge :
        (if k ∈ (L e).1 then e.1
          else lpReplicaCurrentEdgeReflect G sites e.1) = c.1 := by
      rw [hEc] at hedgeCopy
      simpa only [x, lpReplicaOrbitFourColorSlotEdge,
        lpReplicaOrbitFourColorSlotStateOfTag_allocation] using hedgeCopy
    by_cases hk : k ∈ (L e).1
    · left
      have hcEdge : c.1 = e.1 := by simpa only [if_pos hk] using hedge.symm
      rcases c with ⟨ce, a⟩
      dsimp only at hcEdge
      subst ce
      refine ⟨a, hc, ?_⟩
      dsimp only [E, x] at hEc
      rw [lpReplicaProfileCopyEquivCommonSlot_strict] at hEc
      have hpair := Sum.inr.inj hEc
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
    · right
      have hcEdge : c.1 = lpReplicaCurrentEdgeReflect G sites e.1 := by
        simpa only [if_neg hk] using hedge.symm
      rcases c with ⟨ce, a⟩
      dsimp only at hcEdge
      subst ce
      refine ⟨a, hc, ?_⟩
      dsimp only [E, x] at hEc
      rw [lpReplicaProfileCopyEquivCommonSlot_reflectStrict] at hEc
      have hpair := Sum.inr.inj hEc
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
  · rintro (⟨a, ha, hak⟩ | ⟨a, ha, hak⟩)
    · apply (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mpr
      have hslot : E ⟨e.1, a⟩ = x := by
        dsimp only [E, x]
        rw [lpReplicaProfileCopyEquivCommonSlot_strict, hak]
      rw [← hslot, E.symm_apply_apply]
      exact ha
    · apply (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mpr
      have hslot : E
          ⟨lpReplicaCurrentEdgeReflect G sites e.1, a⟩ = x := by
        dsimp only [E, x]
        rw [lpReplicaProfileCopyEquivCommonSlot_reflectStrict, hak]
      rw [← hslot, E.symm_apply_apply]
      exact ha




noncomputable def lpReplicaOrbitSpatialSelectorOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1)) :=
  fun e =>
    ((lpReplicaProfileOrbitSelectedLabelOfCopies
      G sites q m hm P L).2 e).1.1 ∪
    ((lpReplicaProfileOrbitSelectedLabelOfCopies
      G sites q m hm P L).2 e).2.1



def lpReplicaOrbitFourColorSlotReflectFamily
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1)))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := fun e => s.allocation e ∆ P e
  color := s.color



theorem lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotReflectFamily G sites q
      (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation =
    (lpReplicaProfileOrbitSlotMove G sites q
      (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber G sites q m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)
        (lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L)).1).allocation := by
  classical
  funext e
  let selected := lpReplicaProfileOrbitSelectedLabelOfCopies
    G sites q m hm P L
  let R := (selected.2 e).1.1
  let T := (selected.2 e).2.1
  have hselected : selected.1 = L := rfl
  have hR : R ⊆ (L e).1 := by
    simpa only [R, hselected] using (selected.2 e).1.2.1
  have hT : T ⊆ Finset.univ \ (L e).1 := by
    simpa only [T, hselected] using (selected.2 e).2.2.1
  change (L e).1 ∆ (R ∪ T) =
    ((selected.1 e).1 \ R) ∪ T
  rw [hselected]
  ext k
  have hTnot : k ∈ T -> k ∉ (L e).1 := by
    intro hkT
    exact (Finset.mem_sdiff.mp (hT hkT)).2
  by_cases hkL : k ∈ (L e).1 <;>
    by_cases hkR : k ∈ R <;>
      by_cases hkT : k ∈ T
  all_goals simp_all [Finset.mem_symmDiff]
  exact hkL (hR hkR)



theorem lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L) e).1) =
      (lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag)).allocation := by
  rw [lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation]
  rfl


theorem lpReplicaOrbitFourColorSlotReflectFamily_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1))) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotReflectFamily G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotReflectFamily]
  · rfl




def lpReplicaOrbitFourColorSlotReflect
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := fun e => s.allocation e ∆
    lpReplicaOrbitFourColorSelectedStrictSlots G sites q P e
  color := s.color


theorem lpReplicaOrbitFourColorSlotReflect_eq_reflectFamily
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflect G sites q P s =
      lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitFourColorSelectedStrictSlots G sites q P) s := by
  rfl



theorem lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflect G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) s =
      lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) s := by
  refine LPReplicaOrbitFourColorSlotState.ext ?_ rfl
  funext e
  change s.allocation e ∆
      lpReplicaOrbitFourColorSelectedStrictSlots G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) e =
    s.allocation e ∆
      lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P e
  rw [lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies]
  rfl



theorem lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L) e).1) =
      (lpReplicaOrbitFourColorSlotReflect G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag)).allocation := by
  rw [lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies]
  exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
    G sites q m hm L P tag


def lpReplicaOrbitFourColorSlotCrossRecolor
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P X Y : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotRecolor G sites q X Y
    (lpReplicaOrbitFourColorSlotReflect G sites q P s)



def lpReplicaOrbitFourColorSlotCrossToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotRowToggle G sites q P
    (lpReplicaOrbitFourColorSlotReflect G sites q P s)

@[simp] theorem lpReplicaOrbitFourColorSlotRecolor_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (X Y : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOrbitFourColorSlotRecolor G sites q X Y s).allocation =
      s.allocation := rfl


theorem lpReplicaOrbitFourColorSlotRecolor_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (X Y : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotRecolor G sites q X Y) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · exact balancedSwap_involutive Finset.univ X Y s.color


theorem lpReplicaOrbitFourColorSlotReflect_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive (lpReplicaOrbitFourColorSlotReflect G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotReflect]
  · rfl



theorem lpReplicaOrbitFourColorSlotCrossRecolor_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P X Y : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotCrossRecolor G sites q P X Y) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotCrossRecolor,
      lpReplicaOrbitFourColorSlotRecolor,
      lpReplicaOrbitFourColorSlotReflect]
  · exact balancedSwap_involutive Finset.univ X Y s.color


theorem lpReplicaOrbitFourColorSlotCrossToggle_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q)) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotCrossToggle G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · change (lpReplicaOrbitFourColorSlotReflect G sites q P
        (lpReplicaOrbitFourColorSlotReflect G sites q P s)).allocation =
      s.allocation
    exact congrArg (fun z => z.allocation)
      (lpReplicaOrbitFourColorSlotReflect_involutive G sites q P s)
  · change (lpReplicaOrbitFourColorSlotRowToggle G sites q P
        (lpReplicaOrbitFourColorSlotRowToggle G sites q P s)).color =
      s.color
    exact congrArg (fun z => z.color)
      (lpReplicaOrbitFourColorSlotRowToggle_involutive G sites q P s)


theorem lpReplicaOrbitFourColorSlotCrossToggle_comp
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q P
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Q s) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q (P ∆ Q) s := by
  classical
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    ext k
    have hpq :
        ((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P ∆ Q) ↔
          (((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P ∧
              (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∉ Q) ∨
            ((Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ Q ∧
              (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∉ P)) :=
      Finset.mem_symmDiff
    simp only [lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSelectedStrictSlots,
      Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases ha : k ∈ s.allocation e <;>
      by_cases hp : (Sum.inr ⟨e, k⟩ :
        LPReplicaOrbitCommonSlot G sites q) ∈ P <;>
      by_cases hq : (Sum.inr ⟨e, k⟩ :
        LPReplicaOrbitCommonSlot G sites q) ∈ Q
    all_goals simp [ha, hp, hq]
    all_goals tauto
  · funext x
    change (if x.1 ∈ P then lpReplicaRowToggleFin4
          (if x.1 ∈ Q then lpReplicaRowToggleFin4 (s.color x)
            else s.color x)
        else if x.1 ∈ Q then lpReplicaRowToggleFin4 (s.color x)
          else s.color x) =
      if x.1 ∈ P ∆ Q then lpReplicaRowToggleFin4 (s.color x)
        else s.color x
    by_cases hp : x.1 ∈ P <;> by_cases hq : x.1 ∈ Q
    · have hpq : x.1 ∉ P ∆ Q := by
        rw [Finset.mem_symmDiff]
        simp [hp, hq]
      simp only [hp, if_pos, hq, hpq]
      exact lpReplicaRowToggleFin4_involutive (s.color x)
    · have hpq : x.1 ∈ P ∆ Q := (Finset.mem_symmDiff.mpr
        (Or.inl ⟨hp, hq⟩))
      simp only [hp, if_pos, hq, hpq]
      simp
    · have hpq : x.1 ∈ P ∆ Q := (Finset.mem_symmDiff.mpr
        (Or.inr ⟨hq, hp⟩))
      simp only [hp, hq, if_pos, hpq]
      simp
    · have hpq : x.1 ∉ P ∆ Q := by
        rw [Finset.mem_symmDiff]
        simp [hp, hq]
      simp only [hp, hq, hpq]
      simp


noncomputable def lpReplicaOrbitFourColorSlotRowMask
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOrbitCommonSlot G sites q) := by
  classical
  exact Finset.univ.filter fun x =>
    (lpReplicaRowTagEquivFin4.symm
      (s.color ⟨x, Finset.mem_univ _⟩)).1 = true


theorem lpReplicaOrbitFourColorSlotRowMask_crossToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) =
      lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P := by
  classical
  ext x
  by_cases hp : x ∈ P
  · simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and, lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect, hp, if_pos,
      lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst,
      Finset.mem_symmDiff, not_true_eq_false, and_false, true_and]
    cases (lpReplicaRowTagEquivFin4.symm
      (s.color ⟨x, Finset.mem_univ _⟩)).1 <;> simp
  · simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and, lpReplicaOrbitFourColorSlotCrossToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect, hp, if_neg,
      Finset.mem_symmDiff, not_false_eq_true, and_true]
    tauto



noncomputable def lpReplicaOrbitFourColorSlotCrossNormalize
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotCrossToggle G sites q
    (lpReplicaOrbitFourColorSlotRowMask G sites q s) s


theorem lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossNormalize G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) =
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
  rw [lpReplicaOrbitFourColorSlotCrossNormalize,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    lpReplicaOrbitFourColorSlotCrossToggle_comp]
  unfold lpReplicaOrbitFourColorSlotCrossNormalize
  congr 1
  ext x
  simp



theorem lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q s)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q s) = s := by
  exact lpReplicaOrbitFourColorSlotCrossToggle_involutive G sites q
    (lpReplicaOrbitFourColorSlotRowMask G sites q s) s



theorem lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    s = t ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s =
          lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧
        lpReplicaOrbitFourColorSlotRowMask G sites q s =
          lpReplicaOrbitFourColorSlotRowMask G sites q t := by
  constructor
  · intro h
    exact ⟨congrArg (lpReplicaOrbitFourColorSlotCrossNormalize G sites q) h,
      congrArg (lpReplicaOrbitFourColorSlotRowMask G sites q) h⟩
  · rintro ⟨hnorm, hrow⟩
    calc
      s = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q s)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q s) :=
        (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
          G sites q s).symm
      _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q t)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q t) := by
        rw [hrow, hnorm]
      _ = t := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q t


theorem lpReplicaOrbitFourColorSlotCrossToggle_eq_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q P s =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q Q t ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s =
          lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧
        lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P =
          lpReplicaOrbitFourColorSlotRowMask G sites q t ∆ Q := by
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq,
    lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle,
    lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle]



theorem exists_crossToggle_eq_iff_crossNormalize_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    (∃ P : Finset (LPReplicaOrbitCommonSlot G sites q),
        t = lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q t =
        lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
  constructor
  · rintro ⟨P, rfl⟩
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q P s
  · intro hnorm
    let Rs := lpReplicaOrbitFourColorSlotRowMask G sites q s
    let Rt := lpReplicaOrbitFourColorSlotRowMask G sites q t
    refine ⟨Rt ∆ Rs, ?_⟩
    have h := congrArg
      (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt) hnorm
    change lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt t) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rs s) at h
    rw [lpReplicaOrbitFourColorSlotCrossToggle_involutive,
      lpReplicaOrbitFourColorSlotCrossToggle_comp] at h
    exact h




theorem lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {α β : Type*}
    (encode : α -> LPReplicaOrbitFourColorSlotState G sites q)
    (selector : α -> Finset (LPReplicaOrbitCommonSlot G sites q))
    (branch : α -> β)
    (hencode : Function.Injective encode)
    (hstable : forall a b,
      (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector a) (encode a)) =
        (branch b, lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector b) (encode b)) ->
      selector a = selector b) :
    Function.Injective fun a =>
      (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (selector a) (encode a)) := by
  intro a b hab
  have hselector : selector a = selector b := hstable a b hab
  have himage :
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector a) (encode a) =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector b) (encode b) := congrArg Prod.snd hab
  apply hencode
  have himage' : lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (selector b) (encode a) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (selector b) (encode b) := by
    simpa only [hselector] using himage
  have hinv := congrArg
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector b))
    himage'
  rw [lpReplicaOrbitFourColorSlotCrossToggle_involutive
      G sites q (selector b) (encode a),
    lpReplicaOrbitFourColorSlotCrossToggle_involutive
      G sites q (selector b) (encode b)] at hinv
  exact hinv



theorem lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).allocation =
      fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L) e).1 := by
  symm
  exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
    G sites q m hm L P tag



theorem lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).color =
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L
        (lpReplicaToggleRows G sites m P tag)).color := by
  change (lpReplicaOrbitFourColorSlotRowToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).color = _
  rw [lpReplicaOrbitFourColorSlotRowToggle_stateOfTag]



theorem lpReplicaOrbitFourColorSlotEdge_reflect_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (q e.1)) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotReflect G sites q P s)
        (Sum.inr ⟨e, k⟩) =
      if (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P then
        lpReplicaCurrentEdgeReflect G sites
          (lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩))
      else lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩) := by
  classical
  by_cases hp : (Sum.inr ⟨e, k⟩ :
      LPReplicaOrbitCommonSlot G sites q) ∈ P <;>
    by_cases ha : k ∈ s.allocation e
  all_goals
    simp [lpReplicaOrbitFourColorSlotEdge,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSelectedStrictSlots,
      Finset.mem_symmDiff, hp, ha]
  exact (lpReplicaCurrentEdgeReflect_involutive G sites e.1).symm


def LPReplicaOrbitFourColorSlotLeftPattern
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (s : LPReplicaOrbitFourColorSlotState G sites q) : Prop :=
  LeftPattern (lpReplicaOrbitFourColorSlotEnds G sites q s) Finset.univ
    A B u v s.color



theorem lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (hleft : LeftPattern
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ
      A B u v (lpReplicaTagFourColor G sites m tag)) :
    LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let s := lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag
  have htransport := leftPattern_lpReplicaFourColorTransport E
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m)
    (lpReplicaOrbitFourColorSlotEnds G sites q s)
    (lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy
      G sites q m hm L tag) A B u v
    (lpReplicaTagFourColor G sites m tag) hleft
  simpa only [LPReplicaOrbitFourColorSlotLeftPattern, s, E,
    lpReplicaFourColorTransport, lpReplicaOrbitFourColorSlotStateOfTag,
    lpReplicaTagFourColor] using htransport





theorem lpReplicaOrbitFourColorSlotLeftPattern_partialReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (tag' : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (hleft : LeftPattern
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
          (lpReplicaPartialReflectProfile G sites m
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m P)))
      Finset.univ A B u v
      (lpReplicaTagFourColor G sites
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P)) tag')) :
    let m' := lpReplicaPartialReflectProfile G sites m
      (StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P)
    let hm' : lpReplicaSymmetrizedProfile G sites m' = q :=
      (lpReplicaSymmetrizedProfile_partialReflect G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux_le
          (lpReplicaCurrentGraph G sites) m P)).trans hm
    let L' := lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L
    let s' := lpReplicaOrbitFourColorSlotStateOfTag
      G sites q m' hm' L' tag'
    s'.allocation =
        (lpReplicaOrbitFourColorSlotReflectFamily G sites q
          (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag)).allocation ∧
      LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v s' := by
  dsimp only
  constructor
  · simpa only [lpReplicaOrbitFourColorSlotStateOfTag_allocation] using
      lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
        G sites q m hm L P tag
  · exact lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
      G sites q _ _ _ tag' A B u v hleft


noncomputable def lpReplicaOrientedFourColorSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    LPReplicaOrbitFourColorSlotState G sites q :=
  lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1 z.1.2
    z.2.2.1.2 (lpReplicaOrientedFourColorTag G sites A B q z)




theorem lpReplicaOrientedFourColorSlotState_injective
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaOrientedFourColorSlotState G sites A B q) := by
  rintro ⟨m, ⟨a, ⟨⟨P, L⟩, ⟨Sa, Sb⟩⟩⟩⟩
    ⟨n, ⟨b, ⟨⟨Q, M⟩, ⟨Ta, Tb⟩⟩⟩⟩ hstate
  have halloc := congrArg
    (fun s : LPReplicaOrbitFourColorSlotState G sites q => s.allocation)
    hstate
  change (fun e => (L e).1) = (fun e => (M e).1) at halloc
  have hmnVal : m.1 = n.1 :=
    lpReplicaProfile_eq_of_orbitLabel_allocation_eq
      G sites q m.1 n.1 m.2 n.2 L M halloc
  have hmn : m = n := Subtype.ext hmnVal
  subst n
  have hLM : L = M := by
    funext e
    apply Subtype.ext
    exact congrFun halloc e
  subst M
  have htag :
      lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
          (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1 =
        lpReplicaOrbitCollisionSplitTag G sites m.1 b.1 Q.1
          (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1 := by
    exact lpReplicaOrbitFourColorSlotStateOfTag_injective
      G sites q m.1 m.2 L hstate
  have habVal : a.1 = b.1 := by
    calc
      a.1 = lpReplicaTaggedOriginProfile G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
            (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1) false :=
        (lpReplicaOrbitCollisionSplitTag_originProfile_false
          G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2
            Sa.1 Sb.1).symm
      _ = lpReplicaTaggedOriginProfile G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 b.1 Q.1
            (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1) false :=
        congrArg (fun tag =>
          lpReplicaTaggedOriginProfile G sites m.1 tag false) htag
      _ = b.1 := lpReplicaOrbitCollisionSplitTag_originProfile_false
        G sites m.1 b.1 Q.1 (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1
  have hab : a = b := Subtype.ext habVal
  subst b
  have hPQVal : P.1 = Q.1 := by
    calc
      P.1 = lpReplicaRowCopies G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 P.1
            (Finset.mem_filter.mp P.2).2 Sa.1 Sb.1) false :=
        (lpReplicaOrbitCollisionSplitTag_rowCopies_false
          G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2
            Sa.1 Sb.1).symm
      _ = lpReplicaRowCopies G sites m.1
          (lpReplicaOrbitCollisionSplitTag G sites m.1 a.1 Q.1
            (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1) false :=
        congrArg (fun tag => lpReplicaRowCopies G sites m.1 tag false) htag
      _ = Q.1 := lpReplicaOrbitCollisionSplitTag_rowCopies_false
        G sites m.1 a.1 Q.1 (Finset.mem_filter.mp Q.2).2 Ta.1 Tb.1
  have hPQ : P = Q := Subtype.ext hPQVal
  subst Q
  have hcurr : (Sa.1, Sb.1) = (Ta.1, Tb.1) :=
    lpReplicaOrbitCollisionSplitTag_currentSubsets_injective
      G sites m.1 a.1 P.1 (Finset.mem_filter.mp P.2).2 htag
  have hSa : Sa = Ta := Subtype.ext (congrArg Prod.fst hcurr)
  have hSb : Sb = Tb := Subtype.ext (congrArg Prod.snd hcurr)
  subst Ta
  subst Tb
  rfl


theorem lpReplicaOrientedFourColorSlotState_leftPattern
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    LPReplicaOrbitFourColorSlotLeftPattern G sites q A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
      (lpReplicaOrientedFourColorSlotState G sites A B q z) := by
  exact lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
    G sites q z.1.1 z.1.2 z.2.2.1.2
    (lpReplicaOrientedFourColorTag G sites A B q z) A
    (B.map lpReplicaCurrentReflect.toEmbedding)
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
    (lpReplicaOrientedFourColorTag_leftPattern G sites A B q z)


def LPReplicaOrbitFourColorSlotRightPattern
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (s : LPReplicaOrbitFourColorSlotState G sites q) : Prop :=
  RightPattern (lpReplicaOrbitFourColorSlotEnds G sites q s) Finset.univ
    A B u v s.color

end

end StatMech.Ising

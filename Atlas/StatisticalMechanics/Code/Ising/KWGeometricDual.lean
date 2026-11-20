/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















import Mathlib.Combinatorics.Graph.Basic
import Code.Lattice.JordanEnclosureDuality
import Code.Lattice.PeierlsHoleFreeBoundary
import Code.Ising.KramersWannierClose
import Code.Walls.fwrfaceregion

open scoped BigOperators
open Finset SimpleGraph Set

namespace StatMech
namespace Ising

open StatMech.Lattice
open StatMech.Walls





abbrev kwg_Edge (P : PlanarZ2Subgraph) := P.G.edgeSet



abbrev kwg_Face (P : PlanarZ2Subgraph) :=
  (whb_faceRegion (imageGraph P)).ConnectedComponent

noncomputable instance kwg_edgeFinite (P : PlanarZ2Subgraph) : Finite (kwg_Edge P) :=
  Set.toFinite P.G.edgeSet

noncomputable instance kwg_vertexFintype (P : PlanarZ2Subgraph) : Fintype P.V :=
  Fintype.ofFinite P.V

noncomputable instance kwg_adjDecidable (P : PlanarZ2Subgraph) : DecidableRel P.G.Adj :=
  Classical.decRel _


noncomputable def kwg_allEdges (P : PlanarZ2Subgraph) : Finset (kwg_Edge P) := by
  classical
  letI : Fintype (kwg_Edge P) := P.G.fintypeEdgeSet
  exact Finset.univ

@[simp] theorem kwg_mem_allEdges (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    e ∈ kwg_allEdges P := by
  classical
  simp [kwg_allEdges]

noncomputable instance kwg_faceFinite (P : PlanarZ2Subgraph) : Finite (kwg_Face P) :=
  jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)

noncomputable instance kwg_faceFintype (P : PlanarZ2Subgraph) : Fintype (kwg_Face P) :=
  Fintype.ofFinite (kwg_Face P)

noncomputable instance kwg_faceDecidableEq (P : PlanarZ2Subgraph) : DecidableEq (kwg_Face P) :=
  Classical.decEq _


noncomputable def kwg_embeddedEdge (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    Sym2 (Site 2) :=
  Sym2.map P.emb e.1



theorem kwg_exists_flankingFaces (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    ∃ f g : Site 2, (hypercubicLattice 2).Adj f g ∧
      sharedPrimalEdge f g = kwg_embeddedEdge P e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : P.G.Adj x y := (SimpleGraph.mem_edgeSet P.G).mp he
      simpa [kwg_embeddedEdge] using jfc_flankingFaces (P.isSub hxy)



noncomputable def kwg_flankLeft (P : PlanarZ2Subgraph) (e : kwg_Edge P) : Site 2 :=
  (kwg_exists_flankingFaces P e).choose


noncomputable def kwg_flankRight (P : PlanarZ2Subgraph) (e : kwg_Edge P) : Site 2 :=
  (kwg_exists_flankingFaces P e).choose_spec.choose

theorem kwg_flanks_adj (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    (hypercubicLattice 2).Adj (kwg_flankLeft P e) (kwg_flankRight P e) :=
  (kwg_exists_flankingFaces P e).choose_spec.choose_spec.1

theorem kwg_flanks_shared (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    sharedPrimalEdge (kwg_flankLeft P e) (kwg_flankRight P e) = kwg_embeddedEdge P e :=
  (kwg_exists_flankingFaces P e).choose_spec.choose_spec.2






noncomputable def kwg_dualEnds (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    Sym2 (kwg_Face P) :=
  s((whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankLeft P e),
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankRight P e))




noncomputable def kwg_dualGraph (P : PlanarZ2Subgraph) :
    Graph (kwg_Face P) (kwg_Edge P) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := kwg_dualEnds P e = s(x, y)
  isLink_symm := by
    intro e _ x y h
    simpa only [Sym2.eq_swap] using h
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rw [hxy] at hvw
    exact (Sym2.eq_iff.mp hvw).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  edge_mem_iff_exists_isLink := by
    intro e
    simp only [Set.mem_univ, true_iff]
    induction kwg_dualEnds P e with
    | _ x y => exact ⟨x, y, rfl⟩
  left_mem_of_isLink := by simp

@[simp] theorem kwg_dualGraph_vertexSet (P : PlanarZ2Subgraph) :
    (kwg_dualGraph P).vertexSet = Set.univ := rfl

@[simp] theorem kwg_dualGraph_edgeSet (P : PlanarZ2Subgraph) :
    (kwg_dualGraph P).edgeSet = Set.univ := rfl

theorem kwg_dualGraph_isLink_iff (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (x y : kwg_Face P) :
    (kwg_dualGraph P).IsLink e x y ↔ kwg_dualEnds P e = s(x, y) := Iff.rfl



theorem kwg_unique_outerFace (P : PlanarZ2Subgraph) :
    ∃! C : kwg_Face P, C.supp.Infinite :=
  jfc_whb_unique_infinite_component P



theorem kwg_card_face_eq_faceCount (P : PlanarZ2Subgraph) :
    Nat.card (kwg_Face P) = faceCount P.G := by
  obtain ⟨e⟩ := jed_faithfulDiscreteJordan P
  have hbounded :
      Nat.card {c : kwg_Face P // c.supp.Finite} = nullity P.G := by
    rw [Nat.card_congr e, Nat.card_fin]
  have hb : whc_faithfulRegionCount P = nullity P.G := by
    simpa only [whc_faithfulRegionCount] using hbounded
  have htotal := jfc_whb_bounded_add_one_eq_card P
  calc
    Nat.card (kwg_Face P) = whc_faithfulRegionCount P + 1 := htotal.symm
    _ = nullity P.G + 1 := congrArg (fun n => n + 1) hb
    _ = faceCount P.G := rfl


theorem kwg_card_edge_eq_ncard (P : PlanarZ2Subgraph) :
    Nat.card (kwg_Edge P) = P.G.edgeSet.ncard :=
  Nat.card_coe_set_eq P.G.edgeSet









def kwg_isSplit {V : Type*} (c : V → Bool) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y => c x ≠ c y, by
    intro x y
    apply propext
    exact ne_comm⟩

@[simp] theorem kwg_isSplit_mk {V : Type*} (c : V → Bool) (x y : V) :
    kwg_isSplit c s(x, y) ↔ c x ≠ c y := Iff.rfl

theorem kwg_isSplit_iff_bond_neg {V : Type*} (c : ConfigSpace V) (e : Sym2 V) :
    kwg_isSplit c e ↔ bond c e = -1 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [kwg_isSplit_mk, bond_mk]
      unfold spin
      cases c x <;> cases c y <;> norm_num

noncomputable instance kwg_isSplitDecidable {V : Type*} (c : V → Bool) (e : Sym2 V) :
    Decidable (kwg_isSplit c e) :=
  Classical.propDecidable _


def kwg_incidentMod2 {V : Type*} (v : V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y => (x = v ∧ y ≠ v) ∨ (y = v ∧ x ≠ v), by
    intro x y
    apply propext
    constructor <;> rintro (h | h)
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl ⟨h.1, h.2⟩⟩

noncomputable instance kwg_incidentMod2Decidable {V : Type*} [DecidableEq V]
    (v : V) (e : Sym2 V) : Decidable (kwg_incidentMod2 v e) :=
  Classical.propDecidable _

@[simp] theorem kwg_incidentMod2_mk {V : Type*} (v x y : V) :
    kwg_incidentMod2 v s(x, y) ↔
      (x = v ∧ y ≠ v) ∨ (y = v ∧ x ≠ v) := Iff.rfl





theorem kwg_incident_iff_componentCut (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (C : kwg_Face P) :
    kwg_incidentMod2 C (kwg_dualEnds P e) ↔
      kwg_embeddedEdge P e ∈ jed_cutSet
        (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) := by
  rw [← kwg_flanks_shared P e]
  rw [jed_mem_cutSet_iff _ (kwg_flanks_adj P e)]
  unfold kwg_dualEnds
  rw [kwg_incidentMod2_mk]
  tauto


theorem kwg_componentCut_subset_imageGraph (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) ⊆
      (imageGraph P).edgeSet := by
  rintro _ ⟨a, b, hab, rfl, hsplit⟩
  by_contra hn
  have hw : (whb_faceRegion (imageGraph P)).Adj a b := ⟨hab, hn⟩
  have heq := ConnectedComponent.connectedComponentMk_eq_of_adj hw
  change ((whb_faceRegion (imageGraph P)).connectedComponentMk a = C ↔
    ¬ (whb_faceRegion (imageGraph P)).connectedComponentMk b = C) at hsplit
  rw [heq] at hsplit
  tauto



theorem kwg_componentCut_even (P : PlanarZ2Subgraph) (C : kwg_Face P) (v : Site 2) :
    Even (jce_degree
      (jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) v) :=
  jed_cutSet_even _ v


noncomputable def kwg_componentBoundaryGraph (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    SimpleGraph P.V where
  Adj x y := P.G.Adj x y ∧
    Sym2.map P.emb s(x, y) ∈
      jed_cutSet (fun z => (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)
  symm := by
    rintro x y ⟨hxy, hmem⟩
    refine ⟨hxy.symm, ?_⟩
    rwa [Sym2.eq_swap]
  loopless := ⟨fun x h => P.G.irrefl h.1⟩

noncomputable instance kwg_componentBoundaryGraph_locallyFinite
    (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    SimpleGraph.LocallyFinite (kwg_componentBoundaryGraph P C) := fun _ =>
  Fintype.ofFinite _


theorem kwg_componentBoundaryGraph_degree (P : PlanarZ2Subgraph) (C : kwg_Face P)
    (x : P.V) :
    (kwg_componentBoundaryGraph P C).degree x =
      jce_degree
        (jed_cutSet (fun z =>
          (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)) (P.emb x) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : SimpleGraph.LocallyFinite (kwg_componentBoundaryGraph P C) := fun _ =>
    Fintype.ofFinite _
  let E := jed_cutSet (fun z =>
    (whb_faceRegion (imageGraph P)).connectedComponentMk z = C)
  rw [← jed_degree_primalGraph E (P.emb x)]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => P.emb y)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact ⟨P.isSub hy.1, hy.2⟩
  · intro y _ z _ h
    exact P.emb.injective h
  · intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    have hzimg : (imageGraph P).Adj (P.emb x) z := by
      have hcut : s(P.emb x, z) ∈ E := hz.2
      have himg := kwg_componentCut_subset_imageGraph P C hcut
      rwa [SimpleGraph.mem_edgeSet] at himg
    obtain ⟨a, b, hab, ha, hb⟩ := (imageGraph_adj P (P.emb x) z).mp hzimg
    have hax : a = x := P.emb.injective (ha.trans rfl)
    subst a
    refine ⟨b, ?_, hb⟩
    rw [SimpleGraph.mem_neighborFinset]
    refine ⟨hab, ?_⟩
    change s(P.emb x, P.emb b) ∈ E
    rw [hb]
    exact hz.2


theorem kwg_componentBoundaryGraph_even (P : PlanarZ2Subgraph) (C : kwg_Face P)
    (x : P.V) : Even ((kwg_componentBoundaryGraph P C).degree x) := by
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : SimpleGraph.LocallyFinite (kwg_componentBoundaryGraph P C) := fun _ =>
    Fintype.ofFinite _
  rw [kwg_componentBoundaryGraph_degree P C x]
  exact kwg_componentCut_even P C (P.emb x)


noncomputable def kwg_cutSet {V E : Type*} [Finite E]
    (ends : E → Sym2 V) (c : V → Bool) : Finset E := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  exact Finset.univ.filter (fun e => kwg_isSplit c (ends e))

@[simp] theorem kwg_mem_cutSet {V E : Type*} [Finite E]
    (ends : E → Sym2 V) (c : V → Bool) (e : E) :
    e ∈ kwg_cutSet ends c ↔ kwg_isSplit c (ends e) := by
  classical
  simp [kwg_cutSet]


noncomputable def kwg_IsEven {V E : Type*}
    (ends : E → Sym2 V) (F : Finset E) : Prop := by
  classical
  exact ∀ v : V, Even (F.filter (fun e => kwg_incidentMod2 v (ends e))).card

noncomputable instance kwg_isEvenDecidable {V E : Type*}
    (ends : E → Sym2 V) (F : Finset E) : Decidable (kwg_IsEven ends F) :=
  Classical.propDecidable _


noncomputable def kwg_degree {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) (v : V) : ℕ := by
  classical
  exact (F.filter (fun e => kwg_incidentMod2 v (ends e))).card

theorem kwg_IsEven_iff_degree {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) :
    kwg_IsEven ends F ↔ ∀ v, Even (kwg_degree ends F v) := by
  rfl


theorem kwg_IsEven_sdiff {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F S : Finset E} (hSF : S ⊆ F)
    (hF : kwg_IsEven ends F) (hS : kwg_IsEven ends S) :
    kwg_IsEven ends (F \ S) := by
  classical
  intro v
  let p : E → Prop := fun e => kwg_incidentMod2 v (ends e)
  have hfilter :
      (F \ S).filter p = F.filter p \ S.filter p := by
    ext e
    by_cases hp : p e <;> simp [hp]
  rw [hfilter, Finset.card_sdiff]
  have hinter : S.filter p ∩ F.filter p = S.filter p :=
    Finset.inter_eq_left.mpr (Finset.filter_subset_filter p hSF)
  rw [hinter]
  have hle : (S.filter p).card ≤ (F.filter p).card :=
    Finset.card_le_card (Finset.filter_subset_filter p hSF)
  rw [Nat.even_sub hle]
  exact ⟨fun _ => hS v, fun _ => hF v⟩

theorem kwg_degree_insert {V E : Type*} [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) (e : E) (he : e ∉ F) (v : V) :
    kwg_degree ends (insert e F) v = kwg_degree ends F v +
      (if kwg_incidentMod2 v (ends e) then 1 else 0) := by
  classical
  unfold kwg_degree
  rw [Finset.filter_insert]
  by_cases hv : kwg_incidentMod2 v (ends e)
  · rw [if_pos hv, Finset.card_insert_of_notMem (by simp [he]), if_pos hv]
  · rw [if_neg hv, if_neg hv, add_zero]





noncomputable def kwg_isingZ {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → Sym2 V) (β : ℝ) : ℝ :=
  ∑ c : ConfigSpace V, Real.exp (β * ∑ e : E, bond c (ends e))



theorem kwg_prod_bond_eq_prod_pow_degree {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (c : ConfigSpace V) (F : Finset E) :
    (∏ e ∈ F, bond c (ends e)) = ∏ v : V, (spin c v) ^ (kwg_degree ends F v) := by
  classical
  induction F using Finset.induction with
  | empty => simp [kwg_degree]
  | @insert e F he ih =>
      rw [Finset.prod_insert he, ih]
      simp_rw [kwg_degree_insert ends F e he, pow_add]
      rw [Finset.prod_mul_distrib, mul_comm]
      congr 1
      induction ends e using Sym2.inductionOn with
      | _ x y =>
          by_cases hxy : x = y
          · subst y
            rw [bond_mk]
            have hs : spin c x * spin c x = 1 := spin_sq c x
            rw [hs]
            symm
            apply Finset.prod_eq_one
            intro v _
            have hi : ¬ kwg_incidentMod2 v s(x, x) := by
              simp [kwg_incidentMod2_mk]
            rw [if_neg hi, pow_zero]
          · rw [bond_mk]
            have hcvt : ∀ v : V,
                (spin c v) ^ (if kwg_incidentMod2 v s(x, y) then 1 else 0) =
                  if v ∈ ({x, y} : Finset V) then spin c v else 1 := by
              intro v
              have hi : kwg_incidentMod2 v s(x, y) ↔ v ∈ ({x, y} : Finset V) := by
                simp only [kwg_incidentMod2_mk, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (⟨rfl, hy⟩ | ⟨rfl, hx⟩)
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                · rintro (rfl | rfl)
                  · exact Or.inl ⟨rfl, Ne.symm hxy⟩
                  · exact Or.inr ⟨rfl, hxy⟩
              by_cases hv : v ∈ ({x, y} : Finset V)
              · rw [if_pos hv, if_pos (hi.mpr hv), pow_one]
              · rw [if_neg hv, if_neg (fun h => hv (hi.mp h)), pow_zero]
            symm
            calc
              (∏ v : V, (spin c v) ^
                  (if kwg_incidentMod2 v s(x, y) then 1 else 0)) =
                  ∏ v : V, if v ∈ ({x, y} : Finset V) then spin c v else 1 := by
                    apply Finset.prod_congr rfl
                    intro v _
                    exact hcvt v
              _ = spin c x * spin c y := by
                rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pair hxy]




theorem kwg_even_split_card {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (c : V → Bool)
    (hev : kwg_IsEven ends F) :
    Even (F.filter (fun e => kwg_isSplit c (ends e))).card := by
  classical
  have hprod := kwg_prod_bond_eq_prod_pow_degree ends c F
  have hrhs : (∏ v : V, (spin c v) ^ (kwg_degree ends F v)) = (1 : ℝ) := by
    apply Finset.prod_eq_one
    intro v _
    obtain ⟨k, hk⟩ := (kwg_IsEven_iff_degree ends F).mp hev v
    rw [hk, pow_add, ← mul_pow, spin_sq, one_pow]
  have hlhs : (∏ e ∈ F, bond c (ends e)) =
      (-1 : ℝ) ^ (F.filter (fun e => kwg_isSplit c (ends e))).card := by
    calc
      (∏ e ∈ F, bond c (ends e)) =
          ∏ e ∈ F, if kwg_isSplit c (ends e) then (-1 : ℝ) else 1 := by
            apply Finset.prod_congr rfl
            intro e he
            by_cases h : kwg_isSplit c (ends e)
            · rw [if_pos h, (kwg_isSplit_iff_bond_neg c (ends e)).mp h]
            · rw [if_neg h]
              rcases bond_eq_one_or_neg_one c (ends e) with hb | hb
              · exact hb
              · exact (h ((kwg_isSplit_iff_bond_neg c (ends e)).mpr hb)).elim
      _ = (-1 : ℝ) ^ (F.filter (fun e => kwg_isSplit c (ends e))).card := by
        rw [← Finset.prod_filter]
        simp
  rw [hrhs] at hprod
  rw [hlhs] at hprod
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)).mp hprod




noncomputable def kwg_imageHom (P : PlanarZ2Subgraph) : P.G →g imageGraph P where
  toFun := P.emb
  map_rel' := by
    intro x y hxy
    exact ⟨x, y, hxy, rfl, rfl⟩


noncomputable def kwg_latticeWalk (P : PlanarZ2Subgraph) {x y : P.V}
    (p : P.G.Walk x y) :
    (hypercubicLattice 2).Walk (P.emb x) (P.emb y) :=
  (p.map (kwg_imageHom P)).mapLe (imageGraph_le_lattice P)




theorem kwg_faceInside_eq_of_regionReachable (P : PlanarZ2Subgraph) {x : P.V}
    (p : P.G.Walk x x) {a b : Site 2}
    (hab : (whb_faceRegion (imageGraph P)).Reachable a b) :
    (fwr_faceInside (kwg_latticeWalk P p) a ↔
      fwr_faceInside (kwg_latticeWalk P p) b) := by
  classical
  rcases hab with ⟨q⟩
  induction q with
  | nil => rfl
  | @cons u v w huv q ih =>
      have hnot : sharedPrimalEdge u v ∉ (kwg_latticeWalk P p).edges := by
        intro hmem
        have hmem' : sharedPrimalEdge u v ∈ (p.map (kwg_imageHom P)).edges := by
          rw [show (kwg_latticeWalk P p).edges =
            (p.map (kwg_imageHom P)).edges from
              SimpleGraph.Walk.edges_mapLe_eq_edges _ _] at hmem
          exact hmem
        have himg : sharedPrimalEdge u v ∈ (imageGraph P).edgeSet := by
          exact (p.map (kwg_imageHom P)).edges_subset_edgeSet hmem'
        exact huv.2 himg
      have hsame : fwr_faceInside (kwg_latticeWalk P p) u ↔
          fwr_faceInside (kwg_latticeWalk P p) v := by
        have hflip := fwr_faceCutFlip (kwg_latticeWalk P p) huv.1
        have hzero : (kwg_latticeWalk P p).edges.count (sharedPrimalEdge u v) = 0 :=
          List.count_eq_zero.mpr hnot
        rw [hzero] at hflip
        simp only [Nat.not_odd_zero, iff_false] at hflip
        tauto
      exact hsame.trans ih



noncomputable def kwg_walkFaceColour (P : PlanarZ2Subgraph) {x : P.V}
    (p : P.G.Walk x x) : kwg_Face P → Bool := by
  classical
  exact fun C => decide (fwr_faceInside (kwg_latticeWalk P p) C.out)



theorem kwg_walkFaceColour_split_iff_odd (P : PlanarZ2Subgraph) {x : P.V}
    (p : P.G.Walk x x) (e : kwg_Edge P) :
    kwg_isSplit (kwg_walkFaceColour P p) (kwg_dualEnds P e) ↔
      Odd ((kwg_latticeWalk P p).edges.count (kwg_embeddedEdge P e)) := by
  classical
  let R := whb_faceRegion (imageGraph P)
  let L := kwg_flankLeft P e
  let U := kwg_flankRight P e
  have hL : fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk L).out) ↔
      fwr_faceInside (kwg_latticeWalk P p) L := by
    apply kwg_faceInside_eq_of_regionReachable P p
    exact ConnectedComponent.exact (R.connectedComponentMk L).out_eq
  have hU : fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk U).out) ↔
      fwr_faceInside (kwg_latticeWalk P p) U := by
    apply kwg_faceInside_eq_of_regionReachable P p
    exact ConnectedComponent.exact (R.connectedComponentMk U).out_eq
  rw [kwg_dualEnds, kwg_isSplit_mk]
  simp only [kwg_walkFaceColour]
  change decide (fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk L).out)) ≠
    decide (fwr_faceInside (kwg_latticeWalk P p)
      ((R.connectedComponentMk U).out)) ↔ _
  have hflip := fwr_faceCutFlip (kwg_latticeWalk P p) (kwg_flanks_adj P e)
  rw [kwg_flanks_shared P e] at hflip
  change (fwr_faceInside (kwg_latticeWalk P p) L ↔
    ¬ fwr_faceInside (kwg_latticeWalk P p) U) ↔ _ at hflip
  have hsides :
      (decide (fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk L).out)) ≠
        decide (fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk U).out))) ↔
      (fwr_faceInside (kwg_latticeWalk P p) L ↔
        ¬ fwr_faceInside (kwg_latticeWalk P p) U) := by
    by_cases hLo : fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk L).out) <;>
      by_cases hUo : fwr_faceInside (kwg_latticeWalk P p) ((R.connectedComponentMk U).out) <;>
      by_cases hLf : fwr_faceInside (kwg_latticeWalk P p) L <;>
      by_cases hUf : fwr_faceInside (kwg_latticeWalk P p) U <;> simp_all
  exact hsides.trans hflip


theorem kwg_even_sum_iff_even_odd_filter {E : Type*} [DecidableEq E]
    (F : Finset E) (n : E → ℕ) :
    Even (∑ e ∈ F, n e) ↔ Even (F.filter (fun e => Odd (n e))).card := by
  classical
  have hne : (-1 : ℤ) ≠ 1 := by norm_num
  rw [← neg_one_pow_eq_one_iff_even hne, ← neg_one_pow_eq_one_iff_even hne]
  rw [← Finset.prod_pow_eq_pow_sum]
  have hprod : (∏ e ∈ F, (-1 : ℤ) ^ n e) =
      (-1 : ℤ) ^ (F.filter (fun e => Odd (n e))).card := by
    calc
      (∏ e ∈ F, (-1 : ℤ) ^ n e) =
          ∏ e ∈ F, if Odd (n e) then (-1 : ℤ) else 1 := by
            apply Finset.prod_congr rfl
            intro e _
            by_cases ho : Odd (n e)
            · rw [if_pos ho, ho.neg_one_pow]
            · rw [if_neg ho]
              exact Even.neg_one_pow ((Nat.even_or_odd (n e)).resolve_right ho)
      _ = (-1 : ℤ) ^ (F.filter (fun e => Odd (n e))).card := by
        rw [← Finset.prod_filter]
        simp
  rw [hprod]


theorem kwg_walkParity_eq_decide_odd_countP {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (D : Finset (Sym2 V)) {x y : V} (p : G.Walk x y) :
    walkParity G D p =
      decide (Odd (p.edges.countP (fun e => decide (e ∈ D)))) := by
  simp only [Nat.odd_iff]
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
      rw [walkParity_cons, SimpleGraph.Walk.edges_cons, List.countP_cons, ih]
      by_cases hm : s(u, v) ∈ D
      · rw [decide_eq_true hm]
        simp only [Bool.true_xor]
        rcases Nat.mod_two_eq_zero_or_one
            (q.edges.countP (fun e => decide (e ∈ D))) with hn | hn
        · have hs : (q.edges.countP (fun e => decide (e ∈ D)) + 1) % 2 = 1 := by
            omega
          simp [hn, hs]
        · have hs : (q.edges.countP (fun e => decide (e ∈ D)) + 1) % 2 = 0 := by
            omega
          simp [hn, hs]
      · rw [decide_eq_false hm]
        simp


theorem kwg_latticeWalk_count (P : PlanarZ2Subgraph) {x y : P.V}
    (p : P.G.Walk x y) (e : Sym2 P.V) :
    (kwg_latticeWalk P p).edges.count (Sym2.map P.emb e) = p.edges.count e := by
  rw [show (kwg_latticeWalk P p).edges =
    List.map (Sym2.map P.emb) p.edges by
      have h1 := SimpleGraph.Walk.edges_map
        (f := SimpleGraph.Hom.ofLE (imageGraph_le_lattice P))
        (p := p.map (kwg_imageHom P))
      have h2 := SimpleGraph.Walk.edges_map (f := kwg_imageHom P) (p := p)
      unfold kwg_latticeWalk SimpleGraph.Walk.mapLe
      exact h1.trans (by
        rw [h2, List.map_map]
        apply congrArg (fun f => List.map f p.edges)
        funext z
        induction z using Sym2.inductionOn with
        | _ a b => rfl)]
  exact List.count_map_of_injective p.edges (Sym2.map P.emb)
    (Sym2.map.injective P.emb.injective) e


noncomputable def kwg_primalEdgeFinset (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) : Finset (Sym2 P.V) :=
  F.map ⟨Subtype.val, Subtype.val_injective⟩


noncomputable def kwg_primalEnds (P : PlanarZ2Subgraph) (e : kwg_Edge P) : Sym2 P.V := e.1


theorem kwg_primal_incident_iff_mem (P : PlanarZ2Subgraph) (e : kwg_Edge P) (x : P.V) :
    kwg_incidentMod2 x (kwg_primalEnds P e) ↔ x ∈ e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := fun h => by
        subst v
        exact P.G.irrefl ((SimpleGraph.mem_edgeSet P.G).mp he)
      simp only [kwg_primalEnds, kwg_incidentMod2_mk, Sym2.mem_iff]
      constructor
      · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, huv.symm⟩
        · exact Or.inr ⟨rfl, huv⟩

@[simp] theorem kwg_mem_primalEdgeFinset (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (e : kwg_Edge P) :
    e.1 ∈ kwg_primalEdgeFinset P F ↔ e ∈ F := by
  classical
  simp [kwg_primalEdgeFinset]


theorem kwg_sum_count_eq_countP {A : Type*} [DecidableEq A]
    (D : Finset A) (l : List A) :
    (∑ a ∈ D, l.count a) = l.countP (fun a => decide (a ∈ D)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.countP_cons]
      simp_rw [List.count_cons]
      rw [Finset.sum_add_distrib, ih]
      by_cases ha : a ∈ D
      · simp [ha]
      · simp [ha]




theorem kwg_dualEven_evenOnCycles (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (hev : kwg_IsEven (kwg_dualEnds P) F) :
    EvenOnCycles P.G (kwg_primalEdgeFinset P F) := by
  classical
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  intro x p
  have hs := kwg_even_split_card (kwg_dualEnds P) F (kwg_walkFaceColour P p) hev
  have hfilter :
      F.filter (fun e => kwg_isSplit (kwg_walkFaceColour P p) (kwg_dualEnds P e)) =
        F.filter (fun e => Odd (p.edges.count e.1)) := by
    apply Finset.filter_congr
    intro e _
    rw [kwg_walkFaceColour_split_iff_odd P p e]
    change Odd ((kwg_latticeWalk P p).edges.count (Sym2.map P.emb e.1)) ↔ _
    rw [kwg_latticeWalk_count P p e.1]
  rw [hfilter] at hs
  have hsum : Even (∑ e ∈ F, p.edges.count e.1) :=
    (kwg_even_sum_iff_even_odd_filter F (fun e => p.edges.count e.1)).mpr hs
  have hcount : Even
      (p.edges.countP (fun e => decide (e ∈ kwg_primalEdgeFinset P F))) := by
    rw [← kwg_sum_count_eq_countP (kwg_primalEdgeFinset P F) p.edges]
    rw [kwg_primalEdgeFinset, Finset.sum_map]
    exact hsum
  rw [kwg_walkParity_eq_decide_odd_countP]
  have hnot : ¬ Odd
      (p.edges.countP (fun e => decide (e ∈ kwg_primalEdgeFinset P F))) := by
    intro hodd
    obtain ⟨a, ha⟩ := hcount
    obtain ⟨b, hb⟩ := hodd
    omega
  rw [decide_eq_false hnot]




noncomputable def kwg_componentPath {V : Type*} (G : SimpleGraph V) (v : V) :
    G.Walk (G.connectedComponentMk v).out v :=
  (ConnectedComponent.exact (G.connectedComponentMk v).out_eq).some


noncomputable def kwg_componentParityColour {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (D : Finset (Sym2 V)) : V → Bool :=
  fun v => walkParity G D (kwg_componentPath G v)

theorem kwg_walkParity_copy {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : Finset (Sym2 V)} {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') :
    walkParity G D (p.copy hu hv) = walkParity G D p := by
  subst u'
  subst v'
  rfl



theorem kwg_componentParityColour_adj_xor {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {D : Finset (Sym2 V)} (hev : EvenOnCycles G D)
    {x y : V} (hxy : G.Adj x y) :
    (kwg_componentParityColour G D x).xor (kwg_componentParityColour G D y) =
      decide (s(x, y) ∈ D) := by
  classical
  have hC : G.connectedComponentMk x = G.connectedComponentMk y :=
    ConnectedComponent.sound hxy.reachable
  let px := kwg_componentPath G x
  let py := kwg_componentPath G y
  let qxy : G.Walk x y := SimpleGraph.Walk.cons hxy (.nil : G.Walk y y)
  have hroots : (G.connectedComponentMk x).out = (G.connectedComponentMk y).out :=
    congrArg Quot.out hC
  let py' : G.Walk (G.connectedComponentMk x).out y := py.copy hroots.symm rfl
  let via : G.Walk (G.connectedComponentMk x).out y := px.append qxy
  have hpar : walkParity G D py' = walkParity G D via :=
    walkParity_eq_of_evenOnCycles hev py' via
  have hpy : walkParity G D py' = kwg_componentParityColour G D y := by
    change walkParity G D (py.copy hroots.symm rfl) = walkParity G D py
    exact kwg_walkParity_copy py hroots.symm rfl
  have hvia : walkParity G D via =
      (kwg_componentParityColour G D x).xor (decide (s(x, y) ∈ D)) := by
    rw [walkParity_append, walkParity_singleton]
    rfl
  rw [hpy, hvia] at hpar
  rw [hpar]
  cases kwg_componentParityColour G D x <;>
    cases decide (s(x, y) ∈ D) <;> rfl



theorem kwg_exists_colour_of_evenOnCycles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {D : Finset (Sym2 V)}
    (hsub : D ⊆ G.edgeFinset) (hev : EvenOnCycles G D) :
    ∃ c : V → Bool, cutEdges G c = D := by
  classical
  let c := kwg_componentParityColour G D
  refine ⟨c, ?_⟩
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : G.Adj x y
      · rw [mem_cutEdges_iff G c hxy]
        have hx := kwg_componentParityColour_adj_xor hev hxy
        by_cases hm : s(x, y) ∈ D
        · rw [decide_eq_true hm] at hx
          constructor
          · exact fun _ => hm
          · intro _
            cases hc1 : c x <;> cases hc2 : c y <;> simp_all [c]
        · rw [decide_eq_false hm] at hx
          constructor
          · intro hne
            cases hc1 : c x <;> cases hc2 : c y <;> simp_all [c]
          · exact fun h => (hm h).elim
      · have hD : s(x, y) ∉ D := by
          intro hm
          have := hsub hm
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
          exact hxy this
        have hdis : s(x, y) ∉ cutEdges G c := by
          intro hm
          have := (Finset.filter_subset _ _) hm
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
          exact hxy this
        simp [hD, hdis]



theorem kwg_dualEven_exists_primalCut (P : PlanarZ2Subgraph)
    (F : Finset (kwg_Edge P)) (hev : kwg_IsEven (kwg_dualEnds P) F) :
    ∃ c : ConfigSpace P.V, kwg_cutSet (kwg_primalEnds P) c = F := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  have hsub : kwg_primalEdgeFinset P F ⊆ P.G.edgeFinset := by
    intro e he
    rw [kwg_primalEdgeFinset, Finset.mem_map] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset]
    exact f.2
  obtain ⟨c, hc⟩ := kwg_exists_colour_of_evenOnCycles hsub
    (kwg_dualEven_evenOnCycles P F hev)
  refine ⟨c, ?_⟩
  apply Finset.ext
  intro e
  simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : P.G.Adj x y := (SimpleGraph.mem_edgeSet P.G).mp he
      change c x ≠ c y ↔ ⟨s(x, y), he⟩ ∈ F
      rw [← mem_cutEdges_iff P.G c hxy, hc]
      exact kwg_mem_primalEdgeFinset P F ⟨s(x, y), he⟩



theorem kwg_componentIncident_isEven (P : PlanarZ2Subgraph) (C : kwg_Face P) : by
    classical
    letI : Fintype P.V := Fintype.ofFinite P.V
    letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
    exact kwg_IsEven (kwg_primalEnds P)
      ((kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  intro x
  have hcard :
      (((kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))).filter
          (fun e => kwg_incidentMod2 x (kwg_primalEnds P e))).card =
        ((kwg_componentBoundaryGraph P C).incidenceFinset x).card := by
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      rw [Finset.mem_filter] at he
      have hcut := (kwg_incident_iff_componentCut P e C).mp
        (Finset.mem_filter.mp he.1).2
      have hedge : e.1 ∈ (kwg_componentBoundaryGraph P C).edgeSet := by
        rcases e with ⟨e, hedge⟩
        induction e using Sym2.inductionOn with
        | _ u v =>
            rw [SimpleGraph.mem_edgeSet]
            exact ⟨(SimpleGraph.mem_edgeSet P.G).mp hedge, hcut⟩
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset]
      exact ⟨hedge, (kwg_primal_incident_iff_mem P e x).mp he.2⟩
    · intro e _ f _ hef
      exact Subtype.ext hef
    · intro g hg
      rw [SimpleGraph.incidenceFinset_eq_filter, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset] at hg
      have hdata : g ∈ P.G.edgeSet ∧
          Sym2.map P.emb g ∈ jed_cutSet (fun z =>
            (whb_faceRegion (imageGraph P)).connectedComponentMk z = C) := by
        induction g using Sym2.inductionOn with
        | _ u v =>
            have hb := (SimpleGraph.mem_edgeSet
              (kwg_componentBoundaryGraph P C)).mp hg.1
            exact ⟨(SimpleGraph.mem_edgeSet P.G).mpr hb.1, hb.2⟩
      let e : kwg_Edge P := ⟨g, hdata.1⟩
      refine ⟨e, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨?_, (kwg_primal_incident_iff_mem P e x).mpr hg.2⟩
      rw [Finset.mem_filter]
      exact ⟨kwg_mem_allEdges P e, (kwg_incident_iff_componentCut P e C).mpr hdata.2⟩
  rw [hcard, SimpleGraph.card_incidenceFinset_eq_degree]
  exact kwg_componentBoundaryGraph_even P C x



theorem kwg_primalCut_isEven (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    kwg_IsEven (kwg_dualEnds P) (kwg_cutSet (kwg_primalEnds P) c) := by
  classical
  intro C
  let B : Finset (kwg_Edge P) :=
    (kwg_allEdges P).filter (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))
  have hs := kwg_even_split_card (kwg_primalEnds P) B c
    (kwg_componentIncident_isEven P C)
  have heq :
      (kwg_cutSet (kwg_primalEnds P) c).filter
          (fun e => kwg_incidentMod2 C (kwg_dualEnds P e)) =
        B.filter (fun e => kwg_isSplit c (kwg_primalEnds P e)) := by
    ext e
    simp only [B, kwg_cutSet, Finset.mem_filter, Finset.mem_univ, kwg_mem_allEdges, true_and]
    tauto
  change Even ((kwg_cutSet (kwg_primalEnds P) c).filter
    (fun e => kwg_incidentMod2 C (kwg_dualEnds P e))).card
  rw [heq]
  exact hs



theorem kwg_sum_prod_bond {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (F : Finset E) :
    (∑ c : ConfigSpace V, ∏ e ∈ F, bond c (ends e)) =
      if kwg_IsEven ends F then (2 : ℝ) ^ Fintype.card V else 0 := by
  classical
  have hstep : ∀ c : ConfigSpace V,
      (∏ e ∈ F, bond c (ends e)) =
        ∏ v ∈ Finset.univ.filter (fun v => ¬ Even (kwg_degree ends F v)), spin c v := by
    intro c
    rw [kwg_prod_bond_eq_prod_pow_degree ends c F]
    simp_rw [spin_pow c]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v _
    by_cases h : Even (kwg_degree ends F v) <;> simp [h]
  simp_rw [hstep]
  rw [sum_prod_spin_set]
  by_cases hev : kwg_IsEven ends F
  · rw [if_pos hev, if_pos]
    rw [Finset.filter_eq_empty_iff]
    intro v _
    exact not_not_intro ((kwg_IsEven_iff_degree ends F).mp hev v)
  · rw [if_neg hev, if_neg]
    rw [kwg_IsEven_iff_degree, not_forall] at hev
    obtain ⟨v, hv⟩ := hev
    exact Finset.ne_empty_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)



theorem kwg_isingZ_high_temp {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (ends : E → Sym2 V) (β : ℝ) :
    kwg_isingZ ends β =
      (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ Fintype.card E *
        ∑ F : Finset E, if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0 := by
  classical
  unfold kwg_isingZ
  have hweight : ∀ c : ConfigSpace V,
      Real.exp (β * ∑ e : E, bond c (ends e)) =
        (Real.cosh β) ^ Fintype.card E *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) := by
    intro c
    rw [Finset.mul_sum, Real.exp_sum]
    calc
      (∏ e : E, Real.exp (β * bond c (ends e))) =
          ∏ e : E, (Real.cosh β * (1 + Real.tanh β * bond c (ends e))) := by
            apply Finset.prod_congr rfl
            intro e _
            exact exp_mul_eq_cosh_mul β (bond c (ends e))
              (bond_eq_one_or_neg_one c (ends e))
      _ = (∏ _e : E, Real.cosh β) *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) :=
            (Finset.prod_mul_distrib (s := (Finset.univ : Finset E))
              (f := fun _e => Real.cosh β)
              (g := fun e => 1 + Real.tanh β * bond c (ends e)))
      _ = (Real.cosh β) ^ Fintype.card E *
          ∏ e : E, (1 + Real.tanh β * bond c (ends e)) := by
            rw [Finset.prod_const, Finset.card_univ]
  simp_rw [hweight]
  have hexpand : ∀ c : ConfigSpace V,
      (∏ e : E, (1 + Real.tanh β * bond c (ends e))) =
        ∑ F : Finset E, ∏ e ∈ F, (Real.tanh β * bond c (ends e)) := by
    intro c
    simpa using Finset.prod_one_add (s := (Finset.univ : Finset E))
      (f := fun e => Real.tanh β * bond c (ends e))
  simp_rw [hexpand]
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (2 : ℝ) ^ Fintype.card V * (Real.cosh β) ^ Fintype.card E *
      ∑ F : Finset E, (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0) =
    (Real.cosh β) ^ Fintype.card E *
      ((2 : ℝ) ^ Fintype.card V *
        ∑ F : Finset E, (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0)) by ring]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  have hpull : ∀ c : ConfigSpace V,
      (∏ e ∈ F, (Real.tanh β * bond c (ends e))) =
        (Real.tanh β) ^ F.card * ∏ e ∈ F, bond c (ends e) := by
    intro c
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  rw [← Finset.mul_sum]
  have hsum := kwg_sum_prod_bond ends F
  calc
    (Real.tanh β) ^ F.card * (∑ c : ConfigSpace V, ∏ e ∈ F, bond c (ends e)) =
        (Real.tanh β) ^ F.card *
          (if kwg_IsEven ends F then (2 : ℝ) ^ Fintype.card V else 0) :=
      congrArg (fun z => (Real.tanh β) ^ F.card * z) hsum
    _ = (2 : ℝ) ^ Fintype.card V *
        (if kwg_IsEven ends F then (Real.tanh β) ^ F.card else 0) := by
      by_cases hev : kwg_IsEven ends F <;> simp [hev, mul_comm]




noncomputable def kwg_CutEvenMatching {Vp Vd E : Type*} [Fintype Vp] [Fintype Vd]
    [Fintype E] [DecidableEq Vp] [DecidableEq Vd] [DecidableEq E]
    (primalEnds : E → Sym2 Vp) (dualEnds : E → Sym2 Vd) (t mult : ℝ) : Prop := by
  classical
  exact (∑ c : Vp → Bool, t ^ (kwg_cutSet primalEnds c).card) =
    mult * ∑ F : Finset E, if kwg_IsEven dualEnds F then t ^ F.card else 0



theorem kwg_primalCut_card (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    (kwg_cutSet (kwg_primalEnds P) c).card = (cutEdges P.G c).card := by
  classical
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    rw [kwg_cutSet, Finset.mem_filter] at he
    rw [cutEdges, Finset.mem_filter]
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨e.2, (kwg_isSplit_iff_bond_neg c e.1).mp he.2⟩
  · intro e _ f _ h
    exact Subtype.ext h
  · intro g hg
    have hgedge : g ∈ P.G.edgeSet := by
      rw [cutEdges, Finset.mem_filter] at hg
      rw [SimpleGraph.mem_edgeFinset] at hg
      exact hg.1
    let e : kwg_Edge P := ⟨g, hgedge⟩
    refine ⟨e, ?_, rfl⟩
    simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cutEdges, Finset.mem_filter] at hg
    exact (kwg_isSplit_iff_bond_neg c g).mpr hg.2



theorem kwg_primalEdgeFinset_cutSet (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) c) = cutEdges P.G c := by
  classical
  apply Finset.ext
  intro g
  constructor
  · intro hg
    rw [kwg_primalEdgeFinset, Finset.mem_map] at hg
    obtain ⟨e, he, rfl⟩ := hg
    rw [kwg_cutSet, Finset.mem_filter] at he
    rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨e.2, (kwg_isSplit_iff_bond_neg c e.1).mp he.2⟩
  · intro hg
    have hedge : g ∈ P.G.edgeSet := by
      rw [cutEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at hg
      exact hg.1
    let e : kwg_Edge P := ⟨g, hedge⟩
    rw [kwg_primalEdgeFinset, Finset.mem_map]
    refine ⟨e, ?_, rfl⟩
    simp only [kwg_cutSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cutEdges, Finset.mem_filter] at hg
    exact (kwg_isSplit_iff_bond_neg c g).mpr hg.2


theorem kwg_cutSet_eq_iff_cutEdges_eq (P : PlanarZ2Subgraph) (c d : ConfigSpace P.V) :
    kwg_cutSet (kwg_primalEnds P) c = kwg_cutSet (kwg_primalEnds P) d ↔
      cutEdges P.G c = cutEdges P.G d := by
  constructor
  · intro h
    rw [← kwg_primalEdgeFinset_cutSet P c, ← kwg_primalEdgeFinset_cutSet P d, h]
  · intro h
    apply Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩
    simpa only [kwg_primalEdgeFinset] using
      (show kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) c) =
        kwg_primalEdgeFinset P (kwg_cutSet (kwg_primalEnds P) d) by
          rw [kwg_primalEdgeFinset_cutSet, kwg_primalEdgeFinset_cutSet, h])


noncomputable def kwg_componentTwist (P : PlanarZ2Subgraph) (c : ConfigSpace P.V)
    (a : P.G.ConnectedComponent → Bool) : ConfigSpace P.V :=
  fun v => if a (P.G.connectedComponentMk v) then c v else !c v

theorem kwg_componentTwist_cutEdges (P : PlanarZ2Subgraph) (c : ConfigSpace P.V)
    (a : P.G.ConnectedComponent → Bool) :
    cutEdges P.G (kwg_componentTwist P c a) = cutEdges P.G c := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : P.G.Adj x y
      · rw [mem_cutEdges_iff P.G _ hxy, mem_cutEdges_iff P.G _ hxy]
        have hcomp : P.G.connectedComponentMk x = P.G.connectedComponentMk y :=
          ConnectedComponent.sound hxy.reachable
        simp only [kwg_componentTwist, hcomp]
        cases a (P.G.connectedComponentMk y) <;> cases c x <;> cases c y <;> simp
      · have hn1 : s(x, y) ∉ cutEdges P.G (kwg_componentTwist P c a) := by
          intro h
          have hedge := (Finset.filter_subset _ _) h
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
          exact hxy hedge
        have hn2 : s(x, y) ∉ cutEdges P.G c := by
          intro h
          have hedge := (Finset.filter_subset _ _) h
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hedge
          exact hxy hedge
        simp [hn1, hn2]


theorem kwg_primalCut_fiber_card (P : PlanarZ2Subgraph) (c : ConfigSpace P.V) :
    (Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c)).card =
        2 ^ Nat.card P.G.ConnectedComponent := by
  classical
  let mapFiber : ConfigSpace P.V → (P.G.ConnectedComponent → Bool) :=
    fun d C => decide (c C.out = d C.out)
  have hcard := Finset.card_bij
    (fun d (_ : d ∈ Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c)) => mapFiber d)
    (s := Finset.univ.filter (fun d : ConfigSpace P.V =>
      kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c))
    (t := (Finset.univ : Finset (P.G.ConnectedComponent → Bool)))
    (by simp)
    (by
      intro d hd e he hmap
      apply funext
      intro v
      have hdcut : cutEdges P.G d = cutEdges P.G c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P d c).mp (Finset.mem_filter.mp hd).2
      have hecut : cutEdges P.G e = cutEdges P.G c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P e c).mp (Finset.mem_filter.mp he).2
      let q := kwg_componentPath P.G v
      have hdprop := agree_walk P.G hdcut.symm q
      have heprop := agree_walk P.G hecut.symm q
      have hroot : (c (P.G.connectedComponentMk v).out = d (P.G.connectedComponentMk v).out) ↔
          (c (P.G.connectedComponentMk v).out = e (P.G.connectedComponentMk v).out) :=
        decide_eq_decide.mp (congrFun hmap (P.G.connectedComponentMk v))
      have hv : (c v = d v) ↔ (c v = e v) :=
        hdprop.symm.trans (hroot.trans heprop)
      cases hc : c v <;> cases hdv : d v <;> cases hev : e v <;> simp_all)
    (by
      intro a _
      let d := kwg_componentTwist P c a
      have hdcut : kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c :=
        (kwg_cutSet_eq_iff_cutEdges_eq P d c).mpr (kwg_componentTwist_cutEdges P c a)
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdcut⟩, ?_⟩
      funext C
      have hC : P.G.connectedComponentMk C.out = C := C.out_eq
      simp only [mapFiber, d, kwg_componentTwist, hC]
      cases a C <;> cases c C.out <;> simp)
  rw [hcard, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    ← Nat.card_eq_fintype_card]


theorem kwg_primalCut_sum (P : PlanarZ2Subgraph) (t : ℝ) : by
    letI : Fintype P.V := Fintype.ofFinite P.V
    exact (∑ c : ConfigSpace P.V, t ^ (kwg_cutSet (kwg_primalEnds P) c).card) =
      ∑ c : ConfigSpace P.V, t ^ (cutEdges P.G c).card := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  apply Finset.sum_congr rfl
  intro c _
  rw [kwg_primalCut_card P c]




def kwg_GeometricCutEvenMatching (P : PlanarZ2Subgraph) (t mult : ℝ) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact kwg_CutEvenMatching (kwg_primalEnds P) (kwg_dualEnds P) t mult






def kwg_GeometricCutCycleDuality (P : PlanarZ2Subgraph) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact ∀ F : Finset (kwg_Edge P),
    kwg_IsEven (kwg_dualEnds P) F ↔
      ∃ c : ConfigSpace P.V, kwg_cutSet (kwg_primalEnds P) c = F




theorem kwg_geometricCutCycleDuality (P : PlanarZ2Subgraph) :
    kwg_GeometricCutCycleDuality P := by
  intro F
  constructor
  · exact kwg_dualEven_exists_primalCut P F
  · rintro ⟨c, rfl⟩
    exact kwg_primalCut_isEven P c




def kwg_ColourSidesConnected {V : Type*} (G : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ b : Bool, ∀ x y : {v : V // c v = b}, (G.induce {v | c v = b}).Reachable x y




theorem kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c d : V → Bool)
    (hcconn : kwg_ColourSidesConnected G c)
    (hsub : cutEdges G d ⊆ cutEdges G c)
    (hne : (cutEdges G d).Nonempty) :
    cutEdges G d = cutEdges G c := by
  classical
  have sideConst : ∀ {a b : V}, c a = c b → d a = d b := by
    intro a b hab
    obtain ⟨w⟩ := hcconn (c a) ⟨a, rfl⟩ ⟨b, hab.symm⟩
    let wG : G.Walk a b :=
      w.map (SimpleGraph.Embedding.induce {v : V | c v = c a}).toHom
    have hwG : ∀ z ∈ wG.support, c z = c a := by
      intro z hz
      change z ∈
        (w.map (SimpleGraph.Embedding.induce {v : V | c v = c a}).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
      exact z'.2
    have propagate : ∀ {q r : V} (p : G.Walk q r),
        (∀ z ∈ p.support, c z = c q) → d q = d r := by
      intro q r p hp
      induction p with
      | nil => rfl
      | @cons x y z hxy p ih =>
          have hcxy : c x = c y := (hp x (by simp)).trans (hp y (by simp)).symm
          have hnotc : s(x, y) ∉ cutEdges G c := by
            rw [mem_cutEdges_iff G c hxy]
            exact fun hne => hne hcxy
          have hnotd : s(x, y) ∉ cutEdges G d := fun hd => hnotc (hsub hd)
          have hdxy : d x = d y := by
            by_contra hne
            exact hnotd ((mem_cutEdges_iff G d hxy).mpr hne)
          exact hdxy.trans (ih (fun z hz => (hp z (by simp [hz])).trans hcxy))
    exact propagate wG hwG
  obtain ⟨e, he⟩ := hne
  have heG : e ∈ G.edgeFinset := Finset.filter_subset _ _ he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : G.Adj x y := by
        rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heG
      have hdxy : d x ≠ d y := (mem_cutEdges_iff G d hxy).mp he
      have hcxy : c x ≠ c y := (mem_cutEdges_iff G c hxy).mp (hsub he)
      apply Finset.ext
      intro f
      induction f using Sym2.inductionOn with
      | _ a b =>
          by_cases habG : G.Adj a b
          · rw [mem_cutEdges_iff G d habG, mem_cutEdges_iff G c habG]
            constructor
            · intro hdab hcab
              exact hdab (sideConst hcab)
            · intro hcab hdab
              have haxay : c a = c x ∨ c a = c y := by
                cases ha : c a <;> cases hx : c x <;> cases hy : c y <;> simp_all
              have hbxby : c b = c x ∨ c b = c y := by
                cases hb : c b <;> cases hx : c x <;> cases hy : c y <;> simp_all
              rcases haxay with hax | hay <;> rcases hbxby with hbx | hby
              · exact hcab (hax.trans hbx.symm)
              · exact hdxy ((sideConst hax).symm.trans (hdab.trans (sideConst hby)))
              · exact hdxy ((sideConst hbx).symm.trans (hdab.symm.trans (sideConst hay)))
              · exact hcab (hay.trans hby.symm)
          · have hnd : s(a, b) ∉ cutEdges G d := by
              intro h
              exact habG (SimpleGraph.mem_edgeFinset.mp ((Finset.filter_subset _ _) h))
            have hnc : s(a, b) ∉ cutEdges G c := by
              intro h
              exact habG (SimpleGraph.mem_edgeFinset.mp ((Finset.filter_subset _ _) h))
            simp [hnd, hnc]


theorem kwg_dualEven_subset_bond_eq (P : PlanarZ2Subgraph) (c : ConfigSpace P.V)
    (hcconn : kwg_ColourSidesConnected P.G c)
    (F : Finset (kwg_Edge P))
    (hsub : F ⊆ kwg_cutSet (kwg_primalEnds P) c) (hne : F.Nonempty)
    (heven : kwg_IsEven (kwg_dualEnds P) F) :
    F = kwg_cutSet (kwg_primalEnds P) c := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  obtain ⟨d, hd⟩ := (kwg_geometricCutCycleDuality P F).mp heven
  have hsub' : kwg_cutSet (kwg_primalEnds P) d ⊆
      kwg_cutSet (kwg_primalEnds P) c := by
    rw [hd]
    exact hsub
  have hcutSub : cutEdges P.G d ⊆ cutEdges P.G c := by
    rw [← kwg_primalEdgeFinset_cutSet P d, ← kwg_primalEdgeFinset_cutSet P c]
    exact Finset.map_subset_map.mpr hsub'
  have hcutNe : (cutEdges P.G d).Nonempty := by
    rw [← kwg_primalEdgeFinset_cutSet P d, hd]
    exact Finset.map_nonempty.mpr hne
  have hcutEq := kwg_cutEdges_eq_of_nonempty_subset_of_colourSidesConnected
    P.G c d hcconn hcutSub hcutNe
  have hindexEq : kwg_cutSet (kwg_primalEnds P) d =
      kwg_cutSet (kwg_primalEnds P) c :=
    (kwg_cutSet_eq_iff_cutEdges_eq P d c).mpr hcutEq
  rw [← hd, hindexEq]





abbrev kwg_SubdivVertex (V E : Type*) := Sum V (E × Bool)


noncomputable def kwg_subdivGraph {V E : Type*} (ends : E → Sym2 V) :
    SimpleGraph (kwg_SubdivVertex V E) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inr (e, false) => v = (ends e).out.1
    | Sum.inl v, Sum.inr (e, true) => v = (ends e).out.2
    | Sum.inr (e, false), Sum.inl v => v = (ends e).out.1
    | Sum.inr (e, true), Sum.inl v => v = (ends e).out.2
    | Sum.inr (e, b), Sum.inr (e', b') => e = e' ∧ b ≠ b'
    | Sum.inl _, Sum.inl _ => False
  symm := by
    intro x y
    rcases x with v | ⟨e, b⟩ <;> rcases y with w | ⟨e', b'⟩
    · simp
    · cases b' <;> simp [eq_comm]
    · cases b <;> simp [eq_comm]
    · cases b <;> cases b' <;> simp [eq_comm]
  loopless := ⟨by
    intro x
    rcases x with v | ⟨e, b⟩
    · simp
    · cases b <;> simp⟩

@[simp] theorem kwg_subdivGraph_face_port_false {V E : Type*} (ends : E → Sym2 V)
    (v : V) (e : E) :
    (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, false)) ↔
      v = (ends e).out.1 := Iff.rfl

@[simp] theorem kwg_subdivGraph_face_port_true {V E : Type*} (ends : E → Sym2 V)
    (v : V) (e : E) :
    (kwg_subdivGraph ends).Adj (Sum.inl v) (Sum.inr (e, true)) ↔
      v = (ends e).out.2 := Iff.rfl

@[simp] theorem kwg_subdivGraph_ports {V E : Type*} (ends : E → Sym2 V)
    (e e' : E) (b b' : Bool) :
    (kwg_subdivGraph ends).Adj (Sum.inr (e, b)) (Sum.inr (e', b')) ↔
      e = e' ∧ b ≠ b' := by cases b <;> cases b' <;> rfl

noncomputable instance kwg_subdivGraph_locallyFinite {V E : Type*} [Finite V] [Finite E]
    (ends : E → Sym2 V) : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
  fun _ => Fintype.ofFinite _


theorem kwg_subdivGraph_port_degree {V E : Type*} [Finite V] [Finite E]
    [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (e : E) (b : Bool) :
    (kwg_subdivGraph ends).degree (Sum.inr (e, b)) = 2 := by
  classical
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    kwg_subdivGraph_locallyFinite ends
  letI : Fintype ((kwg_subdivGraph ends).neighborSet (Sum.inr (e, b))) :=
    Fintype.ofFinite _
  rw [SimpleGraph.degree]
  apply Finset.card_eq_two.mpr
  let v : V := if b then (ends e).out.2 else (ends e).out.1
  refine ⟨Sum.inl v, Sum.inr (e, !b), ?_, ?_⟩
  · simp [v]
  · ext z
    rcases z with w | ⟨e', b'⟩
    · cases b <;> simp [v, kwg_subdivGraph]
    · cases b <;> cases b' <;> simp [kwg_subdivGraph, eq_comm]


theorem kwg_subdivGraph_face_degree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (v : V) :
    (kwg_subdivGraph ends).degree (Sum.inl v) =
      ((Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)).card +
      ((Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)).card := by
  classical
  let A := (Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)
  let B := (Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)
  let p0 : E → kwg_SubdivVertex V E := fun e => Sum.inr (e, false)
  let p1 : E → kwg_SubdivVertex V E := fun e => Sum.inr (e, true)
  have hnb : (kwg_subdivGraph ends).neighborFinset (Sum.inl v) = A.image p0 ∪ B.image p1 := by
    ext z
    rcases z with w | ⟨e, b⟩
    · simp [A, B, p0, p1, kwg_subdivGraph]
    · cases b <;> simp [A, B, p0, p1, kwg_subdivGraph, eq_comm]
  have hp0 : Function.Injective p0 := by
    intro a b h
    simpa [p0] using h
  have hp1 : Function.Injective p1 := by
    intro a b h
    simpa [p1] using h
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective A hp0,
      Finset.card_image_of_injective B hp1]
  · rw [Finset.disjoint_left]
    intro z hz0 hz1
    obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hz0
    obtain ⟨e1, _, h⟩ := Finset.mem_image.mp hz1
    simp [p0, p1] at h

private theorem kwg_card_filter_eq_sum_ite {E : Type*} [DecidableEq E]
    (F : Finset E) (p : E → Prop) [DecidablePred p] :
    (F.filter p).card = ∑ e ∈ F, if p e then 1 else 0 := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | @insert e F he ih =>
      by_cases hp : p e <;> simp [he, hp, ih]



theorem kwg_sum_degree_even {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) :
    Even (∑ v : V, kwg_degree ends F v) := by
  classical
  unfold kwg_degree
  simp_rw [kwg_card_filter_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Finset.even_sum
  intro e he
  rw [← kwg_card_filter_eq_sum_ite (Finset.univ : Finset V)
    (fun v => kwg_incidentMod2 v (ends e))]
  induction ends e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : x = y
      · subst y
        simp [kwg_incidentMod2_mk]
      · have hfilter : (Finset.univ : Finset V).filter
            (fun v => kwg_incidentMod2 v s(x, y)) = {x, y} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            kwg_incidentMod2_mk, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (⟨hx, _⟩ | ⟨hy, _⟩)
            · exact Or.inl hx.symm
            · exact Or.inr hy.symm
          · rintro (hx | hy)
            · exact Or.inl ⟨hx.symm, fun hyv => hxy (hx.symm.trans hyv.symm)⟩
            · exact Or.inr ⟨hy.symm, fun hxv => hxy (hxv.trans hy)⟩
        rw [hfilter, Finset.card_pair hxy]
        exact ⟨1, rfl⟩



noncomputable def kwg_faceSupportGraph {V E : Type*} (ends : E → Sym2 V) :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e : E, ends e = s(x, y)
  symm := by
    rintro x y ⟨hxy, e, he⟩
    exact ⟨hxy.symm, e, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩


def kwg_deleteVertexGraph {V : Type*} (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v
  symm := by
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := ⟨fun x h => G.irrefl h.1⟩



theorem kwg_minimalEven_nonOuter_reachable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (outer : V)
    (hne : Nonempty E) (heven : kwg_IsEven ends Finset.univ)
    (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ)
    {v w : V} (hvout : v ≠ outer) (hwout : w ≠ outer)
    (hvinc : ∃ e : E, kwg_incidentMod2 v (ends e))
    (hwinc : ∃ e : E, kwg_incidentMod2 w (ends e)) :
    (kwg_deleteVertexGraph (kwg_faceSupportGraph ends) outer).Reachable v w := by
  classical
  let H := kwg_deleteVertexGraph (kwg_faceSupportGraph ends) outer
  let inC : V → Prop := fun z => z ≠ outer ∧ H.Reachable v z
  let S : Finset E := Finset.univ.filter fun e =>
    inC (ends e).out.1 ∨ inC (ends e).out.2
  have hC_v : inC v := ⟨hvout, SimpleGraph.Reachable.refl _⟩
  have incident_end {z : V} {e : E} (hinc : kwg_incidentMod2 z (ends e)) :
      z = (ends e).out.1 ∨ z = (ends e).out.2 := by
    have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
    rw [hout, kwg_incidentMod2_mk] at hinc
    rcases hinc with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have incident_ne {z : V} {e : E} (hinc : kwg_incidentMod2 z (ends e)) :
      (ends e).out.1 ≠ (ends e).out.2 := by
    intro heq
    have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
    rw [hout, heq, kwg_incidentMod2_mk] at hinc
    tauto
  have close_edge {a b : V} {e : E} (ha : inC a) (hbout : b ≠ outer)
      (hab : a ≠ b) (he : ends e = s(a, b)) : inC b := by
    refine ⟨hbout, ha.2.trans ?_⟩
    exact (show H.Adj a b from
      ⟨⟨hab, e, he⟩, ha.1, hbout⟩).reachable
  have hSne : S.Nonempty := by
    obtain ⟨e, he⟩ := hvinc
    refine ⟨e, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ e, ?_⟩
    rcases incident_end he with hv | hv
    · exact Or.inl (hv ▸ hC_v)
    · exact Or.inr (hv ▸ hC_v)
  have hnonouter : ∀ z : V, z ≠ outer →
      (S.filter (fun e => kwg_incidentMod2 z (ends e))).card =
        (if inC z then (Finset.univ.filter
          (fun e => kwg_incidentMod2 z (ends e))).card else 0) := by
    intro z hzout
    by_cases hzC : inC z
    · rw [if_pos hzC]
      congr 1
      ext e
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hinc
        refine ⟨?_, hinc⟩
        rcases incident_end hinc with hz | hz
        · exact Or.inl (hz ▸ hzC)
        · exact Or.inr (hz ▸ hzC)
    · rw [if_neg hzC]
      have hempty : S.filter (fun e => kwg_incidentMod2 z (ends e)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e heS hinc
        rw [Finset.mem_filter] at heS
        have hne := incident_ne hinc
        rcases heS.2 with h1 | h2
        · rcases incident_end hinc with hz1 | hz2
          · exact hzC (hz1 ▸ h1)
          · have hout2 : (ends e).out.2 ≠ outer := hz2 ▸ hzout
            exact hzC (hz2 ▸ close_edge h1 hout2 hne (ends e).out_eq.symm)
        · rcases incident_end hinc with hz1 | hz2
          · have hout1 : (ends e).out.1 ≠ outer := hz1 ▸ hzout
            exact hzC (hz1 ▸ close_edge h2 hout1 hne.symm
              ((ends e).out_eq.symm.trans Sym2.eq_swap))
          · exact hzC (hz2 ▸ h2)
      rw [hempty]
      rfl
  have hSeven : kwg_IsEven ends S := by
    intro z
    by_cases hz : z = outer
    · subst z
      change Even (kwg_degree ends S outer)
      have hsum := kwg_sum_degree_even ends S
      have hrest : Even (∑ z : V, if z = outer then 0 else kwg_degree ends S z) := by
        apply Finset.even_sum
        intro z _
        by_cases hz : z = outer
        · simp [hz]
        · simp only [hz, if_false]
          change Even ((S.filter (fun e => kwg_incidentMod2 z (ends e))).card)
          rw [hnonouter z hz]
          by_cases hzC : inC z
          · simpa [hzC] using heven z
          · simp [hzC]
      obtain ⟨a, ha⟩ := hsum
      obtain ⟨b, hb⟩ := hrest
      refine ⟨a - b, ?_⟩
      have hsplit : (∑ z : V, kwg_degree ends S z) =
          kwg_degree ends S outer + ∑ z : V, if z = outer then 0 else kwg_degree ends S z := by
        rw [← Finset.sum_erase_add (Finset.univ : Finset V)
          (fun z => kwg_degree ends S z) (Finset.mem_univ outer), add_comm]
        congr 1
        have hfun : (fun z : V => if z = outer then 0 else kwg_degree ends S z) =
            fun z : V => if z ≠ outer then kwg_degree ends S z else 0 := by
          funext z
          by_cases hz : z = outer <;> simp [hz]
        rw [hfun, ← Finset.sum_filter]
        congr 1
        ext z
        simp [Finset.mem_erase]
      omega
    · rw [hnonouter z hz]
      by_cases hzC : inC z
      · simpa [hzC] using heven z
      · simp [hzC]
  have hSall : S = Finset.univ := hmin S hSne hSeven
  obtain ⟨e, he⟩ := hwinc
  have heS : e ∈ S := hSall.symm ▸ Finset.mem_univ e
  rw [Finset.mem_filter] at heS
  have hne := incident_ne he
  rcases incident_end he with hw | hw <;> rcases heS.2 with h1 | h2
  · simpa [inC, hw] using h1.2
  · have hout1 : (ends e).out.1 ≠ outer := hw ▸ hwout
    simpa [inC, hw] using (close_edge h2 hout1 hne.symm
      ((ends e).out_eq.symm.trans Sym2.eq_swap)).2
  · have hout2 : (ends e).out.2 ≠ outer := hw ▸ hwout
    simpa [inC, hw] using (close_edge h1 hout2 hne (ends e).out_eq.symm).2
  · simpa [inC, hw] using h2.2


theorem kwg_minimalEvenFinset_nonOuter_reachable {V E : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) (outer : V)
    (hne : F.Nonempty) (heven : kwg_IsEven ends F)
    (hmin : ∀ S : Finset E, S ⊆ F → S.Nonempty → kwg_IsEven ends S → S = F)
    {v w : V} (hvout : v ≠ outer) (hwout : w ≠ outer)
    (hvinc : ∃ e ∈ F, kwg_incidentMod2 v (ends e))
    (hwinc : ∃ e ∈ F, kwg_incidentMod2 w (ends e)) :
    (kwg_deleteVertexGraph
      (kwg_faceSupportGraph (fun e : ↑F => ends e.1)) outer).Reachable v w := by
  classical
  let emb : ↑F ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  let e0 : E := hne.choose
  letI : Nonempty ↑F := ⟨⟨e0, hne.choose_spec⟩⟩
  have heven' : kwg_IsEven (fun e : ↑F => ends e.1) Finset.univ := by
    intro z
    have hz := heven z
    have hmap : ((Finset.univ : Finset ↑F).filter
        (fun e => kwg_incidentMod2 z (ends e.1))).map emb =
        F.filter (fun e => kwg_incidentMod2 z (ends e)) := by
      ext e
      simp [emb, and_comm]
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map] at hcard
    exact hcard.symm ▸ hz
  have hmin' : ∀ S : Finset ↑F, S.Nonempty →
      kwg_IsEven (fun e : ↑F => ends e.1) S → S = Finset.univ := by
    intro S hSne hSeven
    let T : Finset E := S.map emb
    have hTsub : T ⊆ F := by
      intro e he
      simp only [T, Finset.mem_map] at he
      obtain ⟨e', _, rfl⟩ := he
      exact e'.2
    have hTne : T.Nonempty := Finset.map_nonempty.mpr hSne
    have hTeven : kwg_IsEven ends T := by
      intro z
      have hz := hSeven z
      have hmap : (S.filter (fun e => kwg_incidentMod2 z (ends e.1))).map emb =
          T.filter (fun e => kwg_incidentMod2 z (ends e)) := by
        ext e
        simp [T, emb, and_comm]
      have hcard := congrArg Finset.card hmap
      rw [Finset.card_map] at hcard
      exact hcard ▸ hz
    have hTF : T = F := hmin T hTsub hTne hTeven
    apply Finset.eq_univ_iff_forall.mpr
    intro e
    have heT : (e : E) ∈ T := hTF.symm ▸ e.2
    simp only [T, Finset.mem_map] at heT
    obtain ⟨e', he'S, he'eq⟩ := heT
    have : e' = e := Subtype.ext he'eq
    simpa [this] using he'S
  apply kwg_minimalEven_nonOuter_reachable (fun e : ↑F => ends e.1) outer
    inferInstance heven' hmin' hvout hwout
  · obtain ⟨e, heF, he⟩ := hvinc
    exact ⟨⟨e, heF⟩, he⟩
  · obtain ⟨e, heF, he⟩ := hwinc
    exact ⟨⟨e, heF⟩, he⟩




theorem kwg_exists_minimalEvenFinset_subset_mem {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F : Finset E} {e : E} (heF : e ∈ F)
    (hF : kwg_IsEven ends F) :
    ∃ S : Finset E, S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧
      ∀ T : Finset E, T ⊆ S → T.Nonempty → kwg_IsEven ends T → T = S := by
  classical
  let C := F.powerset.filter (fun S => e ∈ S ∧ kwg_IsEven ends S)
  have hFC : F ∈ C := by
    simp [C, heF, hF]
  have hCne : C.Nonempty := ⟨F, hFC⟩
  let cards := C.image Finset.card
  have hcardsne : cards.Nonempty := Finset.image_nonempty.mpr hCne
  let m := cards.min' hcardsne
  have hm : m ∈ cards := Finset.min'_mem cards hcardsne
  obtain ⟨S, hSC, hSm⟩ := Finset.mem_image.mp hm
  have hSprops := Finset.mem_filter.mp hSC
  have hSsub : S ⊆ F := Finset.mem_powerset.mp hSprops.1
  have heS : e ∈ S := hSprops.2.1
  have hSeven : kwg_IsEven ends S := hSprops.2.2
  have hSne : S.Nonempty := ⟨e, heS⟩
  refine ⟨S, hSsub, heS, hSne, hSeven, ?_⟩
  intro T hTS hTne hTeven
  have hmS : m = S.card := hSm.symm
  by_cases heT : e ∈ T
  · have hTC : T ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (hTS.trans hSsub), heT, hTeven⟩
    have hTcard : T.card ∈ cards := Finset.mem_image.mpr ⟨T, hTC, rfl⟩
    have hminle : m ≤ T.card := Finset.min'_le cards T.card hTcard
    apply Finset.eq_of_subset_of_card_le hTS
    simpa [hmS] using hminle
  · let R := S \ T
    have hReven : kwg_IsEven ends R :=
      kwg_IsEven_sdiff ends hTS hSeven hTeven
    have heR : e ∈ R := by simp [R, heS, heT]
    have hRsub : R ⊆ F := Finset.sdiff_subset.trans hSsub
    have hRC : R ∈ C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hRsub, heR, hReven⟩
    have hRcard : R.card ∈ cards := Finset.mem_image.mpr ⟨R, hRC, rfl⟩
    have hminle : m ≤ R.card := Finset.min'_le cards R.card hRcard
    have hcard := Finset.card_sdiff_add_card_eq_card hTS
    change R.card + T.card = S.card at hcard
    have hTpos : 0 < T.card := Finset.card_pos.mpr hTne
    omega



theorem kwg_exists_minimalEvenFinset_peel_mem {V E : Type*} [DecidableEq E]
    (ends : E → Sym2 V) {F : Finset E} {e : E} (heF : e ∈ F)
    (hF : kwg_IsEven ends F) :
    ∃ S R : Finset E,
      S ⊆ F ∧ e ∈ S ∧ S.Nonempty ∧ kwg_IsEven ends S ∧
        (∀ T : Finset E, T ⊆ S → T.Nonempty →
          kwg_IsEven ends T → T = S) ∧
        R = F \ S ∧ kwg_IsEven ends R ∧ Disjoint S R ∧ S ∪ R = F := by
  obtain ⟨S, hSF, heS, hSne, hSeven, hSmin⟩ :=
    kwg_exists_minimalEvenFinset_subset_mem ends heF hF
  let R := F \ S
  have hReven : kwg_IsEven ends R :=
    kwg_IsEven_sdiff ends hSF hF hSeven
  have hdisjoint : Disjoint S R := by
    simpa [R] using (Finset.disjoint_sdiff : Disjoint S (F \ S))
  have hunion : S ∪ R = F := by
    simpa [R, Finset.union_comm] using Finset.sdiff_union_of_subset hSF
  exact ⟨S, R, hSF, heS, hSne, hSeven, hSmin, rfl,
    hReven, hdisjoint, hunion⟩



theorem kwg_subdivGraph_face_degree_even {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (heven : kwg_IsEven ends Finset.univ) (v : V) :
    Even ((kwg_subdivGraph ends).degree (Sum.inl v)) := by
  classical
  rw [kwg_subdivGraph_face_degree]
  let A := (Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)
  let B := (Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)
  let I := (Finset.univ : Finset E).filter
    (fun e => kwg_incidentMod2 v (ends e))
  let L := (Finset.univ : Finset E).filter
    (fun e => (ends e).out.1 = v ∧ (ends e).out.2 = v)
  have hcount : A.card + B.card = I.card + 2 * L.card := by
    rw [kwg_card_filter_eq_sum_ite, kwg_card_filter_eq_sum_ite,
      kwg_card_filter_eq_sum_ite, kwg_card_filter_eq_sum_ite]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ e : E, ((if (ends e).out.1 = v then 1 else 0) +
          if (ends e).out.2 = v then 1 else 0) =
          ∑ e : E, ((if kwg_incidentMod2 v (ends e) then 1 else 0) +
            2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
        have hinc : kwg_incidentMod2 v (ends e) ↔
            ((ends e).out.1 = v ∧ (ends e).out.2 ≠ v) ∨
              ((ends e).out.2 = v ∧ (ends e).out.1 ≠ v) := by
          conv_lhs => rw [hout]
          exact kwg_incidentMod2_mk v (ends e).out.1 (ends e).out.2
        by_cases h1 : (ends e).out.1 = v <;>
          by_cases h2 : (ends e).out.2 = v <;> simp [hinc, h1, h2]
      _ = (∑ e : E, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          ∑ e : E, 2 * if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ e : E, if kwg_incidentMod2 v (ends e) then 1 else 0) +
          2 * ∑ e : E, if (ends e).out.1 = v ∧ (ends e).out.2 = v then 1 else 0 := by
        rw [Finset.mul_sum]
  rw [show ((Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)).card = A.card
      from rfl,
    show ((Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)).card = B.card
      from rfl,
    hcount]
  obtain ⟨k, hk⟩ := heven v
  change Even (I.card + 2 * L.card)
  have hI : I.card = k + k := hk
  exact ⟨k + L.card, by omega⟩


theorem kwg_subdivGraph_reachable_port_of_incident {V E : Type*}
    (ends : E → Sym2 V) {v : V} {e : E}
    (hinc : kwg_incidentMod2 v (ends e)) (b : Bool) :
    (kwg_subdivGraph ends).Reachable (Sum.inl v) (Sum.inr (e, b)) := by
  have hout : ends e = s((ends e).out.1, (ends e).out.2) := (ends e).out_eq.symm
  rw [hout, kwg_incidentMod2_mk] at hinc
  rcases hinc with ⟨h1, _⟩ | ⟨h2, _⟩
  · subst v
    cases b
    · exact SimpleGraph.Adj.reachable
        ((kwg_subdivGraph_face_port_false ends _ _).2 rfl)
    · exact (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_face_port_false ends _ _).2 rfl)).trans
        (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_ports ends e e false true).2 ⟨rfl, by decide⟩))
  · subst v
    cases b
    · exact (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_face_port_true ends _ _).2 rfl)).trans
        (SimpleGraph.Adj.reachable
          ((kwg_subdivGraph_ports ends e e true false).2 ⟨rfl, by decide⟩))
    · exact SimpleGraph.Adj.reachable
        ((kwg_subdivGraph_face_port_true ends _ _).2 rfl)


theorem kwg_minimalEven_edgePorts_reachable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V)
    (hne : Nonempty E) (heven : kwg_IsEven ends Finset.univ)
    (hmin : ∀ S : Finset E, S.Nonempty → kwg_IsEven ends S → S = Finset.univ) :
    ∀ e e' : E, ∀ b b' : Bool,
      (kwg_subdivGraph ends).Reachable (Sum.inr (e, b)) (Sum.inr (e', b')) := by
  classical
  let e0 : E := Classical.choice hne
  let G := kwg_subdivGraph ends
  let c := G.connectedComponentMk (Sum.inr (e0, false))
  let S : Finset E := Finset.univ.filter fun e => Sum.inr (e, false) ∈ c.supp
  have hports : ∀ e : E, e ∈ S ↔ Sum.inr (e, false) ∈ c.supp := by
    intro e
    simp [S]
  have hSne : S.Nonempty := by
    refine ⟨e0, (hports e0).2 ?_⟩
    simp [c]
  have hSeven : kwg_IsEven ends S := by
    intro v
    by_cases hv : Sum.inl v ∈ c.supp
    · have hfilter : S.filter (fun e => kwg_incidentMod2 v (ends e)) =
          (Finset.univ : Finset E).filter (fun e => kwg_incidentMod2 v (ends e)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hinc
          refine ⟨(hports e).2 ?_, hinc⟩
          have hvc := (SimpleGraph.ConnectedComponent.mem_supp_iff c (Sum.inl v)).mp hv
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c,
            ← hvc, SimpleGraph.ConnectedComponent.eq]
          exact (kwg_subdivGraph_reachable_port_of_incident ends hinc false).symm
      rw [hfilter]
      exact heven v
    · have hfilter : S.filter (fun e => kwg_incidentMod2 v (ends e)) = ∅ := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨heS, hinc⟩
          exfalso
          apply hv
          have hec := (SimpleGraph.ConnectedComponent.mem_supp_iff c
            (Sum.inr (e, false))).mp ((hports e).1 heS)
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c,
            ← hec, SimpleGraph.ConnectedComponent.eq]
          exact kwg_subdivGraph_reachable_port_of_incident ends hinc false
        · intro he
          simp at he
      rw [hfilter]
      exact Even.zero
  have hSall : S = Finset.univ := hmin S hSne hSeven
  intro e e' b b'
  have he0 : G.Reachable (Sum.inr (e, false)) (Sum.inr (e0, false)) := by
    rw [← SimpleGraph.ConnectedComponent.eq,
      ← SimpleGraph.ConnectedComponent.mem_supp_iff]
    change Sum.inr (e, false) ∈ c.supp
    exact (hports e).1 (hSall.symm ▸ Finset.mem_univ e)
  have he'0 : G.Reachable (Sum.inr (e', false)) (Sum.inr (e0, false)) := by
    rw [← SimpleGraph.ConnectedComponent.eq,
      ← SimpleGraph.ConnectedComponent.mem_supp_iff]
    change Sum.inr (e', false) ∈ c.supp
    exact (hports e').1 (hSall.symm ▸ Finset.mem_univ e')
  have hb0 : G.Reachable (Sum.inr (e, b)) (Sum.inr (e, false)) := by
    cases b
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [G])
  have hb'0 : G.Reachable (Sum.inr (e', b')) (Sum.inr (e', false)) := by
    cases b'
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [G])
  exact hb0.trans (he0.trans (he'0.symm.trans hb'0.symm))



theorem kwg_cutEvenMatching_of_duality (P : PlanarZ2Subgraph) (t mult : ℝ)
    (hdual : kwg_GeometricCutCycleDuality P)
    (hfib : ∀ F : Finset (kwg_Edge P), kwg_IsEven (kwg_dualEnds P) F →
      ((Finset.univ.filter (fun c : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) c = F)).card : ℝ) = mult) :
    kwg_GeometricCutEvenMatching P t mult := by
  classical
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching
  rw [← Finset.sum_fiberwise (s := (Finset.univ : Finset (ConfigSpace P.V)))
    (g := fun c => kwg_cutSet (kwg_primalEnds P) c)
    (f := fun c => t ^ (kwg_cutSet (kwg_primalEnds P) c).card)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  have hinter :
      (∑ c ∈ (Finset.univ : Finset (ConfigSpace P.V)) with
          kwg_cutSet (kwg_primalEnds P) c = F,
          t ^ (kwg_cutSet (kwg_primalEnds P) c).card) =
        ((Finset.univ.filter (fun c : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) c = F)).card : ℝ) * t ^ F.card := by
    calc
      _ = ∑ _c ∈ (Finset.univ.filter (fun c : ConfigSpace P.V =>
          kwg_cutSet (kwg_primalEnds P) c = F)), t ^ F.card := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [Finset.mem_filter] at hc
            rw [hc.2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hinter]
  by_cases hev : kwg_IsEven (kwg_dualEnds P) F
  · rw [if_pos hev, hfib F hev]
  · rw [if_neg hev, mul_zero]
    have hempty : Finset.univ.filter (fun c : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) c = F) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c _ hc
      exact hev ((hdual F).mpr ⟨c, hc⟩)
    rw [hempty, Finset.card_empty]
    norm_num



theorem kwg_geometricCutEvenMatching (P : PlanarZ2Subgraph) (t : ℝ) :
    kwg_GeometricCutEvenMatching P t
      ((2 : ℝ) ^ Nat.card P.G.ConnectedComponent) := by
  classical
  apply kwg_cutEvenMatching_of_duality P t
    ((2 : ℝ) ^ Nat.card P.G.ConnectedComponent) (kwg_geometricCutCycleDuality P)
  intro F hev
  obtain ⟨c, hc⟩ := (kwg_geometricCutCycleDuality P F).mp hev
  have hfilter :
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = F) =
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = kwg_cutSet (kwg_primalEnds P) c) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hc]
  rw [hfilter, kwg_primalCut_fiber_card]
  norm_num



theorem kwg_geometricCutEvenMatching_of_connected (P : PlanarZ2Subgraph)
    (hconn : P.G.Connected) (t : ℝ) : kwg_GeometricCutEvenMatching P t 2 := by
  classical
  letI : Nonempty P.V := hconn.nonempty
  apply kwg_cutEvenMatching_of_duality P t 2 (kwg_geometricCutCycleDuality P)
  intro F hev
  obtain ⟨c, hc⟩ := (kwg_geometricCutCycleDuality P F).mp hev
  have hfilter :
      Finset.univ.filter (fun d : ConfigSpace P.V =>
        kwg_cutSet (kwg_primalEnds P) d = F) =
      Finset.univ.filter (fun d : ConfigSpace P.V => cutEdges P.G d = cutEdges P.G c) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hc, kwg_cutSet_eq_iff_cutEdges_eq]
  rw [hfilter]
  exact_mod_cast fiber_card_eq_two P.G hconn.preconnected rfl





noncomputable def kwg_DualContourMatching (P : PlanarZ2Subgraph)
    (β βstar c : ℝ) : Prop := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  exact Real.tanh βstar = Real.exp (-2 * β) ∧
    (2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) *
        (∑ F : Finset (kwg_Edge P),
          if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0)
      = c * isingZ P.G β 0




theorem kwg_dualContourMatching_of_cutMatching (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) :
    kwg_DualContourMatching P β βstar
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) * 2)) := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  refine ⟨htemp, ?_⟩
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching at hmatch
  rw [kwg_primalCut_sum P] at hmatch
  rw [isingZ_low_temp_expansion P.G β]
  have hedgecard : P.G.edgeFinset.card = P.G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card P.G.edgeSet]
    congr 1
    ext e
    simp
  rw [hedgecard]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0
  have hexp : (0 : ℝ) < Real.exp (β * P.G.edgeFinset.card) := Real.exp_pos _
  change _ * _ * Sd = _
  change _ = 2 * Sd at hmatch
  rw [hmatch]
  field_simp



theorem kwg_isingZ_duality_of_cutMatching (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β))
    (hmatch : kwg_GeometricCutEvenMatching P (Real.exp (-2 * β)) 2) : by
    letI : Fintype P.V := Fintype.ofFinite P.V
    letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
    letI : DecidableEq (kwg_Face P) := Classical.decEq _
    exact kwg_isingZ (kwg_dualEnds P) βstar =
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) * 2)) * isingZ P.G β 0 := by
  classical
  letI : Fintype P.V := Fintype.ofFinite P.V
  letI : Fintype (kwg_Face P) := Fintype.ofFinite (kwg_Face P)
  have hdcm := kwg_dualContourMatching_of_cutMatching P β βstar htemp hmatch
  obtain ⟨_, hdcm⟩ := hdcm
  rw [kwg_isingZ_high_temp]
  simpa only [Nat.card_eq_fintype_card] using hdcm



theorem kwg_isingZ_duality (P : PlanarZ2Subgraph)
    (β βstar : ℝ) (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    kwg_isingZ (kwg_dualEnds P) βstar =
      ((2 : ℝ) ^ Nat.card (kwg_Face P) *
        (Real.cosh βstar) ^ Nat.card (kwg_Edge P) /
        (Real.exp (β * P.G.edgeSet.ncard) *
          (2 : ℝ) ^ Nat.card P.G.ConnectedComponent)) * isingZ P.G β 0 := by
  classical
  have hmatch := kwg_geometricCutEvenMatching P (Real.exp (-2 * β))
  unfold kwg_GeometricCutEvenMatching kwg_CutEvenMatching at hmatch
  rw [kwg_primalCut_sum P] at hmatch
  rw [kwg_isingZ_high_temp, isingZ_low_temp_expansion P.G β]
  have hedgecard : P.G.edgeFinset.card = P.G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card P.G.edgeSet]
    congr 1
    ext e
    simp
  rw [hedgecard]
  rw [← htemp] at hmatch ⊢
  set Sd := ∑ F : Finset (kwg_Edge P),
    if kwg_IsEven (kwg_dualEnds P) F then (Real.tanh βstar) ^ F.card else 0
  set mult : ℝ := (2 : ℝ) ^ Nat.card P.G.ConnectedComponent
  change _ * _ * Sd = _
  change _ = mult * Sd at hmatch
  rw [hmatch]
  have hexp : Real.exp (β * (P.G.edgeSet.ncard : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hmult : mult ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  field_simp
  simp only [Nat.card_eq_fintype_card]
  ring

end Ising
end StatMech

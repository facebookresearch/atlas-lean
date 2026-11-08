/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

@[expose] public section

open scoped Matrix BigOperators



section
namespace MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted

/-!
# Perfect graphs
-/

/-- Finite graph where every induced subgraph has `chromaticNumber = cliqueNum`. -/
def IsPerfect {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (s : Set V), (G.induce s).chromaticNumber = ((G.induce s).cliqueNum : ℕ∞)

/-- Gasparian's condition (P): every finset satisfies `card s ≤ alpha * omega`. -/
def PerfIneq {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.card ≤ (G.induce (↑s : Set V)).indepNum * (G.induce (↑s : Set V)).cliqueNum

/-- Complement commutes with induce. -/
private lemma induce_compl_eq {V : Type*} (G : SimpleGraph V) (s : Set V) :
    Gᶜ.induce s = (G.induce s)ᶜ := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  constructor
  · rintro ⟨hne, hnad⟩
    refine ⟨?_, ?_⟩
    · intro heq
      apply hne
      exact Subtype.ext_iff.mp heq
    · intro hadj
      exact hnad hadj
  · rintro ⟨hne, hnad⟩
    refine ⟨?_, ?_⟩
    · intro heq
      apply hne
      exact Subtype.ext heq
    · exact hnad

/-- Build a coloring of `G[t]` from a separating function on `V`. -/
private lemma colorable_of_fn {V : Type*} (G : SimpleGraph V) (t : Finset V)
    (m : ℕ) (f : V → ℕ) (hbound : ∀ v ∈ t, f v < m)
    (hadj : ∀ u ∈ t, ∀ v ∈ t, G.Adj u v → f u ≠ f v) :
    (G.induce (↑t : Set V)).Colorable m := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun x : ↥(↑t : Set V) => (⟨f (x : V), hbound (x : V) x.property⟩ : Fin m))
    ?_⟩
  intro x y hadj2
  simp only [SimpleGraph.comap_adj] at hadj2
  simp only [ne_eq, Fin.mk.injEq]
  exact hadj (x : V) x.property (y : V) y.property hadj2

/-- Read off a separating function on `V` from a coloring of `G[t]`. -/
private lemma fn_of_colorable {V : Type*} (G : SimpleGraph V) (t : Finset V)
    (m : ℕ) (h : (G.induce (↑t : Set V)).Colorable m) :
    ∃ f : V → ℕ, (∀ v ∈ t, f v < m) ∧
      ∀ u ∈ t, ∀ v ∈ t, G.Adj u v → f u ≠ f v := by
  classical
  obtain ⟨C⟩ := h
  refine ⟨fun v => if hmem : v ∈ t then (C ⟨v, hmem⟩).val else 0, ?_, ?_⟩
  · intro v hv
    simp only [hv, dite_true]
    exact (C ⟨v, hv⟩).isLt
  · intro u hu v hv hadj
    simp only [hu, hv, dite_true]
    intro heq
    have hadj' : (G.induce (↑t : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hadj
    have hne := C.valid hadj'
    apply hne
    exact Fin.val_injective heq

/-- A nonempty finset induces a graph with clique number at least one. -/
private lemma one_le_cliqueNum_of_mem {V : Type*} [Finite V]
    (G : SimpleGraph V) (u : Finset V) (x : V) (hx : x ∈ u) :
    1 ≤ (G.induce (↑u : Set V)).cliqueNum := by
  have := Fintype.ofFinite V
  classical
  have h1 : (G.induce (↑u : Set V)).IsClique
      (↑({⟨x, hx⟩} : Finset (↥(↑u : Set V))) : Set _) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact absurd rfl hab
  have h2 := SimpleGraph.IsClique.card_le_cliqueNum h1
  rw [Finset.card_singleton] at h2
  exact h2

/-- A nonempty finset induces a graph with independence number at least one. -/
private lemma one_le_indepNum_of_mem {V : Type*} [Finite V]
    (G : SimpleGraph V) (u : Finset V) (x : V) (hx : x ∈ u) :
    1 ≤ (G.induce (↑u : Set V)).indepNum := by
  have := Fintype.ofFinite V
  classical
  have h1 : (G.induce (↑u : Set V)).IsIndepSet
      (↑({⟨x, hx⟩} : Finset (↥(↑u : Set V))) : Set _) := by
    intro a ha b hb hne hadj
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
    subst ha
    subst hb
    exact absurd rfl hne
  have h2 := SimpleGraph.IsIndepSet.card_le_indepNum h1
  rw [Finset.card_singleton] at h2
  exact h2

/-- Clique number is monotone in the finset. -/
private lemma cliqueNum_mono_finset {V : Type*} [Finite V] (G : SimpleGraph V)
    {t s : Finset V} (hts : t ⊆ s) :
    (G.induce (↑t : Set V)).cliqueNum ≤ (G.induce (↑s : Set V)).cliqueNum := by
  have := Fintype.ofFinite V
  classical
  obtain ⟨K, hK⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := G.induce (↑t : Set V))
  have hKclique := hK.isClique
  have hKcard := hK.card_eq
  let emb : (↥(↑t : Set V)) → (↥(↑s : Set V)) := fun x => ⟨(x : V), hts x.property⟩
  have hemb_inj : Function.Injective emb := by
    intro a b hab
    have hval : (emb a).val = (emb b).val := Subtype.ext_iff.mp hab
    have hval2 : (a : V) = (b : V) := hval
    exact Subtype.ext hval2
  let K' := Finset.map ⟨emb, hemb_inj⟩ K
  have hK'clique : (G.induce (↑s : Set V)).IsClique (↑K' : Set _) := by
    intro x hx y hy hne
    have hx' : x ∈ K' := Finset.mem_coe.mp hx
    have hy' : y ∈ K' := Finset.mem_coe.mp hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy'
    simp only [SimpleGraph.comap_adj]
    have hab : a ≠ b := by
      intro heq
      apply hne
      rw [heq]
    have hadj := hKclique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
    simpa [SimpleGraph.comap_adj] using hadj
  have hle := SimpleGraph.IsClique.card_le_cliqueNum hK'clique
  rw [Finset.card_map] at hle
  omega

/-- Step 1 (perfect implies P): an omega-coloring has independent color
classes of size at most alpha. Every perfect graph satisfies the `alpha * omega`
bound on every induced finset. -/
theorem perfect_implies_ineq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : IsPerfect G) : PerfIneq G := by
  classical
  intro s
  let H := G.induce (↑s : Set V)
  have hperf : H.chromaticNumber = ((H.cliqueNum : ℕ) : ℕ∞) := hG (↑s : Set V)
  have hcol : H.Colorable H.cliqueNum := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
    rw [hperf]
  obtain ⟨C⟩ := hcol
  let f : (↥(↑s : Set V)) → Fin H.cliqueNum := fun x => C x
  have hindep : ∀ b : Fin H.cliqueNum,
      H.IsIndepSet (↑(Finset.univ.filter (fun a => f a = b)) : Set (↥(↑s : Set V))) := by
    intro b x hx y hy hne hadj
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
      true_and] at hx hy
    have hne2 : C x ≠ C y := C.valid hadj
    have hx' : f x = b := hx
    have hy' : f y = b := hy
    simp only [f] at hx' hy'
    rw [hx', hy'] at hne2
    exact absurd rfl hne2
  have hcard : ∀ b ∈ Finset.image f Finset.univ,
      (Finset.univ.filter (fun a => f a = b)).card ≤ H.indepNum := by
    intro b _
    exact SimpleGraph.IsIndepSet.card_le_indepNum (hindep b)
  have hle : Finset.univ.card ≤ H.indepNum * (Finset.image f Finset.univ).card :=
    Finset.card_le_mul_card_image Finset.univ H.indepNum hcard
  have himg : (Finset.image f Finset.univ).card ≤ H.cliqueNum := by
    calc (Finset.image f Finset.univ).card ≤ Fintype.card (Fin H.cliqueNum) :=
          Finset.card_le_univ _
      _ = H.cliqueNum := Fintype.card_fin _
  have huniv : Fintype.card (↥(↑s : Set V)) = s.card := by simp
  have huniv2 : (Finset.univ : Finset (↥(↑s : Set V))).card = s.card := by
    rw [← huniv, Finset.card_univ]
  calc s.card = (Finset.univ : Finset (↥(↑s : Set V))).card := huniv2.symm
    _ ≤ H.indepNum * (Finset.image f Finset.univ).card := hle
    _ ≤ H.indepNum * H.cliqueNum := by gcongr

/-- (P) is symmetric under complement, since alpha and omega swap. -/
private lemma ineq_compl_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) : PerfIneq G ↔ PerfIneq Gᶜ := by
  classical
  constructor
  · intro h s
    have hs := h s
    rw [induce_compl_eq] at *
    rw [SimpleGraph.cliqueNum_compl, SimpleGraph.indepNum_compl] at *
    -- goal: card s ≤ (Hᶜ).indepNum * (Hᶜ).cliqueNum = H.cliqueNum * H.indepNum
    -- hs: card s ≤ H.indepNum * H.cliqueNum
    rw [mul_comm]
    exact hs
  · intro h s
    have hs := h s
    have e1 : (Gᶜ.induce (↑s : Set V)) = ((G.induce (↑s : Set V))ᶜ) :=
      induce_compl_eq G (↑s : Set V)
    rw [e1, SimpleGraph.cliqueNum_compl, SimpleGraph.indepNum_compl] at hs
    -- hs : card s ≤ clique * indep; goal card s ≤ indep * clique
    have e2 : ((G.induce (↑s : Set V)).cliqueNum * (G.induce (↑s : Set V)).indepNum) =
        ((G.induce (↑s : Set V)).indepNum * (G.induce (↑s : Set V)).cliqueNum) := mul_comm _ _
    rwa [e2] at hs

/-- Step 2(a): deleting a nonempty independent set preserves omega,
else the remainder's coloring extends with one fresh color. -/
private lemma step2a_aux {V : Type*} [Finite V] [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V)
    (ih : ∀ t : Finset V, t ⊂ s →
      (G.induce (↑t : Set V)).Colorable (G.induce (↑t : Set V)).cliqueNum)
    (hncol : ¬ (G.induce (↑s : Set V)).Colorable
      (G.induce (↑s : Set V)).cliqueNum)
    (S : Finset V) (hSS : S ⊆ s) (hne : S.Nonempty)
    (hind : G.IsIndepSet (↑S : Set V)) :
    (G.induce (↑(s \ S) : Set V)).cliqueNum =
      (G.induce (↑s : Set V)).cliqueNum := by
  have := Fintype.ofFinite V
  classical
  have hmono : (G.induce (↑(s \ S) : Set V)).cliqueNum ≤
      (G.induce (↑s : Set V)).cliqueNum :=
    cliqueNum_mono_finset G Finset.sdiff_subset
  have hssub : s \ S ⊂ s := by
    refine Finset.ssubset_iff_of_subset ?_ |>.mpr ?_
    · exact Finset.sdiff_subset
    · obtain ⟨x, hxS⟩ := hne
      refine ⟨x, hSS hxS, ?_⟩
      intro hcon
      exact (Finset.mem_sdiff.mp hcon).2 hxS
  by_contra hlt_ne
  have hlt : (G.induce (↑(s \ S) : Set V)).cliqueNum <
      (G.induce (↑s : Set V)).cliqueNum := by
    omega
  obtain ⟨x0, hx0S⟩ := hne
  have homega_pos : 1 ≤ (G.induce (↑s : Set V)).cliqueNum :=
    one_le_cliqueNum_of_mem G s x0 (hSS hx0S)
  have hcol_rem : (G.induce (↑(s \ S) : Set V)).Colorable
      (G.induce (↑(s \ S) : Set V)).cliqueNum :=
    ih (s \ S) hssub
  obtain ⟨f, hfb, hfa⟩ := fn_of_colorable G (s \ S) _ hcol_rem
  let ω := (G.induce (↑s : Set V)).cliqueNum
  let ωr := (G.induce (↑(s \ S) : Set V)).cliqueNum
  have hωr_le : ωr ≤ ω - 1 := by omega
  refine hncol ?_
  apply colorable_of_fn G s ω (fun v => if v ∈ S then ω - 1 else f v)
  · intro v hv
    by_cases hmv : v ∈ S
    · simp only [ite_eq_left hmv]
      omega
    · simp only [ite_eq_right hmv]
      have hvm : v ∈ s \ S := Finset.mem_sdiff.mpr ⟨hv, hmv⟩
      have h1 := hfb v hvm
      omega
  · intro u hu v hv hadj
    by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
    · have hmem : u ∈ (↑S : Set V) := Finset.mem_coe.mpr huS
      have hmem2 : v ∈ (↑S : Set V) := Finset.mem_coe.mpr hvS
      have hne2 : u ≠ v := G.ne_of_adj hadj
      have hcon := hind hmem hmem2 hne2
      exact absurd hadj hcon
    · simp only [ite_eq_left huS, ite_eq_right hvS]
      intro heq
      have hvm : v ∈ s \ S := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
      have h1 := hfb v hvm
      omega
    · simp only [ite_eq_right huS, ite_eq_left hvS]
      intro heq
      have hum : u ∈ s \ S := Finset.mem_sdiff.mpr ⟨hu, huS⟩
      have h1 := hfb u hum
      omega
    · simp only [ite_eq_right huS, ite_eq_right hvS]
      have hum : u ∈ s \ S := Finset.mem_sdiff.mpr ⟨hu, huS⟩
      have hvm : v ∈ s \ S := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
      exact hfa u hum v hvm hadj

/-- Map a finset of the subtype back to `V`. -/
private noncomputable def subMap {V : Type*} (u : Finset V)
    (s : Finset (↥(↑u : Set V))) : Finset V :=
  open scoped Classical in s.map ⟨Subtype.val, Subtype.val_injective⟩

private lemma subMap_card {V : Type*} (u : Finset V)
    (s : Finset (↥(↑u : Set V))) :
    (subMap u s).card = s.card := by
  simp only [subMap, Finset.card_map]

private lemma subMap_subset {V : Type*} (u : Finset V)
    (s : Finset (↥(↑u : Set V))) :
    subMap u s ⊆ u := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  exact a.property

private lemma indep_subMap {V : Type*} (G : SimpleGraph V) (u : Finset V)
    (s : Finset (↥(↑u : Set V)))
    (h : (G.induce (↑u : Set V)).IsIndepSet (↑s : Set _)) :
    G.IsIndepSet (↑(subMap u s) : Set V) := by
  classical
  intro x hx y hy hne hadj
  have hx' : x ∈ subMap u s := Finset.mem_coe.mp hx
  have hy' : y ∈ subMap u s := Finset.mem_coe.mp hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy'
  have hne2 : a ≠ b := by
    intro heq; apply hne; rw [heq]
  have hadj2 : (G.induce (↑u : Set V)).Adj a b := hadj
  exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne2 hadj2

private lemma clique_subMap {V : Type*} (G : SimpleGraph V) (u : Finset V)
    (s : Finset (↥(↑u : Set V)))
    (h : (G.induce (↑u : Set V)).IsClique (↑s : Set _)) :
    G.IsClique (↑(subMap u s) : Set V) := by
  classical
  intro x hx y hy hne
  have hx' : x ∈ subMap u s := Finset.mem_coe.mp hx
  have hy' : y ∈ subMap u s := Finset.mem_coe.mp hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy'
  have hne2 : a ≠ b := by
    intro heq; apply hne; congr 1
  have hadj2 := h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hne2
  simpa [SimpleGraph.comap_adj] using hadj2

/-- Maximum independent set as a finset of `V`. -/
private lemma exists_maxIndep_finset {V : Type*} (G : SimpleGraph V)
    (u : Finset V) :
    ∃ A0 : Finset V, A0 ⊆ u ∧ A0.card = (G.induce (↑u : Set V)).indepNum ∧
      G.IsIndepSet (↑A0 : Set V) := by
  classical
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G.induce (↑u : Set V))
  refine ⟨subMap u s, subMap_subset u s, ?_, indep_subMap G u s hs.isIndepSet⟩
  rw [subMap_card, hs.card_eq]

/-- Maximum clique as a finset of `V`. -/
private lemma exists_maxClique_finset {V : Type*} (G : SimpleGraph V)
    (u : Finset V) :
    ∃ K : Finset V, K ⊆ u ∧ K.card = (G.induce (↑u : Set V)).cliqueNum ∧
      G.IsClique (↑K : Set V) := by
  classical
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := G.induce (↑u : Set V))
  have hcard : s.card = (G.induce (↑u : Set V)).cliqueNum := hs.card_eq
  refine ⟨subMap u s, subMap_subset u s, ?_, clique_subMap G u s hs.isClique⟩
  rw [subMap_card, hcard]

private lemma card_filter_subtype {V : Type*} [DecidableEq V]
    (u : Finset V) (S : Finset V) (hS : S ⊆ u) :
    (Finset.univ.filter (fun x : ↥(↑u : Set V) => (x : V) ∈ S)).card = S.card := by
  classical
  have h1 : Finset.image Subtype.val
      (Finset.univ.filter (fun x : ↥(↑u : Set V) => (x : V) ∈ S)) = S := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hv
      exact ⟨⟨v, hS hv⟩, hv, rfl⟩
  have h3 : (Finset.image Subtype.val
      (Finset.univ.filter (fun x : ↥(↑u : Set V) => (x : V) ∈ S))).card
      = (Finset.univ.filter (fun x : ↥(↑u : Set V) => (x : V) ∈ S)).card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  rw [h1] at h3
  omega

/-- Step 2(e): the incidence rank argument. If the `A j` meet each `K l`
in exactly one vertex off the diagonal and miss on the diagonal, then
there are at most `u.card` indices. -/
private lemma card_le_of_incid {V : Type*} [Finite V] [DecidableEq V]
    (u : Finset V) (J : Type*) [Fintype J]
    (A K : J → Finset V)
    (hAsub : ∀ j, A j ⊆ u)
    (hN : 2 ≤ Fintype.card J)
    (hdiag : ∀ j, (A j ∩ K j).card = 0)
    (hoff : ∀ j l, j ≠ l → (A j ∩ K l).card = 1) :
    Fintype.card J ≤ u.card := by
  have := Fintype.ofFinite V
  classical
  let M : Matrix J (↥(↑u : Set V)) ℚ :=
    fun j x => if (x : V) ∈ A j then 1 else 0
  let M' : Matrix J (↥(↑u : Set V)) ℚ :=
    fun j x => if (x : V) ∈ K j then 1 else 0
  let N : ℕ := Fintype.card J
  have hentry : ∀ j l, (M * M'ᵀ) j l = if j = l then 0 else 1 := by
    intro j l
    have hmul : (M * M'ᵀ) j l = ∑ x : ↥(↑u : Set V), M j x * M' l x := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    have hunfold : (∑ x : ↥(↑u : Set V), M j x * M' l x)
        = ∑ x : ↥(↑u : Set V), (if (x : V) ∈ A j then (1 : ℚ) else 0) *
          (if (x : V) ∈ K l then (1 : ℚ) else 0) := rfl
    rw [hmul, hunfold]
    have hsum : (∑ x : ↥(↑u : Set V),
          (if (x : V) ∈ A j then (1 : ℚ) else 0) *
          (if (x : V) ∈ K l then (1 : ℚ) else 0))
        = ((A j ∩ K l).card : ℚ) := by
      have hstep : (∑ x : ↥(↑u : Set V),
            (if (x : V) ∈ A j then (1 : ℚ) else 0) *
            (if (x : V) ∈ K l then (1 : ℚ) else 0))
          = Finset.sum
            (Finset.univ.filter
              (fun x : ↥(↑u : Set V) => (x : V) ∈ A j ∩ K l))
            (fun _ => (1 : ℚ)) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases haj : (x : V) ∈ A j <;> by_cases hkl : (x : V) ∈ K l
        · simp [haj, hkl]
        · simp [haj, hkl]
        · simp [haj, hkl]
        · simp [haj, hkl]
      rw [hstep]
      have hinter_sub : A j ∩ K l ⊆ u :=
        (Finset.inter_subset_left).trans (hAsub j)
      have hcard := card_filter_subtype u (A j ∩ K l) hinter_sub
      rw [Finset.sum_const, hcard, nsmul_one]
    rw [hsum]
    by_cases hjl : j = l
    · subst hjl
      rw [hdiag]
      simp
    · rw [hoff _ _ hjl]
      simp [hjl]
  have hmat : M * M'ᵀ = (Matrix.of (fun _ _ => (1 : ℚ)) - 1) := by
    ext j l
    rw [hentry]
    by_cases hjl : j = l <;> simp [hjl, Matrix.of_apply]
  have hNne : (N : ℚ) - 1 ≠ 0 := by
    have h2 : (2 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
    linarith
  let c : ℚ := 1 / ((N : ℚ) - 1)
  have hc : c * ((N : ℚ) - 1) = 1 := by
    simp [c, one_div, inv_mul_cancel₀ hNne]
  have hJJ : (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix J J ℚ) *
      Matrix.of (fun _ _ => (1 : ℚ)) =
      (N : ℚ) • Matrix.of (fun _ _ => (1 : ℚ)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.of_apply, Finset.sum_const,
      Finset.card_univ, N]
  have hleftInv :
      (c • (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix J J ℚ) - 1) *
        (Matrix.of (fun _ _ => (1 : ℚ)) - 1) = 1 := by
    have hexpand :
        (c • (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix J J ℚ) - 1) *
          (Matrix.of (fun _ _ => (1 : ℚ)) - 1)
        = (c * (N : ℚ) - c - 1) •
          (Matrix.of (fun _ _ => (1 : ℚ)) : Matrix J J ℚ) + 1 := by
      rw [sub_mul, mul_sub, mul_sub]
      rw [smul_mul_assoc, hJJ]
      rw [smul_smul]
      rw [mul_one, one_mul, mul_one]
      module
    rw [hexpand]
    have hzero : c * (N : ℚ) - c - 1 = 0 := by
      have hcc : c * ((N : ℚ) - 1) = 1 := hc
      linarith [hcc]
    rw [hzero, zero_smul, zero_add]
  have hunit_det : IsUnit
      (Matrix.of (fun _ _ => (1 : ℚ)) - 1 : Matrix J J ℚ).det :=
    Matrix.isUnit_det_of_left_inverse hleftInv
  have hunit : IsUnit (Matrix.of (fun _ _ => (1 : ℚ)) - 1 : Matrix J J ℚ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunit_det
  have hrank : (M * M'ᵀ).rank = N := by
    rw [hmat]
    exact Matrix.rank_of_isUnit _ hunit
  have hle1 : (M * M'ᵀ).rank ≤ M.rank := Matrix.rank_mul_le_left M M'ᵀ
  have hle2 : M.rank ≤ Fintype.card (↥(↑u : Set V)) :=
    Matrix.rank_le_card_width M
  have hcard_u : Fintype.card (↥(↑u : Set V)) = u.card := by simp
  omega

/-- A clique meets an independent set in at most one vertex. -/
private lemma card_inter_clique_indep_le_one {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A K : Finset V)
    (hA : G.IsIndepSet (↑A : Set V)) (hK : G.IsClique (↑K : Set V)) :
    (A ∩ K).card ≤ 1 := by
  by_contra hle
  simp only [not_le] at hle
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hle
  have haA : a ∈ (↑A : Set V) := Finset.mem_coe.mpr (Finset.mem_inter.mp ha).1
  have haK : a ∈ (↑K : Set V) := Finset.mem_coe.mpr (Finset.mem_inter.mp ha).2
  have hbA : b ∈ (↑A : Set V) := Finset.mem_coe.mpr (Finset.mem_inter.mp hb).1
  have hbK : b ∈ (↑K : Set V) := Finset.mem_coe.mpr (Finset.mem_inter.mp hb).2
  exact hA haA hbA hab (hK haK hbK hab)

/-- An injective map from an `ω`-set into `range ω` covers it. -/
private lemma image_eq_range_of_injOn {V : Type*}
    (f : V → ℕ) (K : Finset V) (ω : ℕ) (hKcard : K.card = ω)
    (hb : ∀ v ∈ K, f v < ω) (hinj : Set.InjOn f (↑K : Set V)) :
    K.image f = Finset.range ω := by
  have himg : (K.image f).card = K.card := Finset.card_image_of_injOn hinj
  have hsub : K.image f ⊆ Finset.range ω := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_range.mpr (hb v hv)
  have himg2 : (K.image f).card = (Finset.range ω).card := by
    rw [himg, hKcard, Finset.card_range]
  exact Finset.eq_of_subset_of_card_le hsub himg2.ge

/-- A fiber over a hit value, under an injective map, is a singleton. -/
private lemma filter_fiber_card_eq_one {V : Type*}
    (f : V → ℕ) (K : Finset V) (c : ℕ) (hc : c ∈ K.image f)
    (hinj : Set.InjOn f (↑K : Set V)) :
    (K.filter (fun v => f v = c)).card = 1 := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
  have hfib : K.filter (fun w => f w = f v) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hwK, hfw⟩
      exact hinj (Finset.mem_coe.mpr hwK) (Finset.mem_coe.mpr hv) hfw
    · rintro rfl
      exact ⟨hv, rfl⟩
  rw [hfib, Finset.card_singleton]

/-- An injective map from an `(ω - 1)`-set into `range ω`, missing `c`,
covers the rest. -/
private lemma image_eq_erase_range_of_injOn {V : Type*}
    (f : V → ℕ) (Kp : Finset V) (ω c : ℕ) (hc : c < ω)
    (hcard : Kp.card = ω - 1) (hb : ∀ v ∈ Kp, f v < ω)
    (hinj : Set.InjOn f (↑Kp : Set V)) (hmiss : c ∉ Kp.image f) :
    Kp.image f = (Finset.range ω).erase c := by
  have himg : (Kp.image f).card = Kp.card := Finset.card_image_of_injOn hinj
  have hsub : Kp.image f ⊆ (Finset.range ω).erase c := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, hb v hv⟩
    intro heq
    apply hmiss
    rw [← heq]
    exact Finset.mem_image_of_mem f hv
  have hcardE : ((Finset.range ω).erase c).card = ω - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hc),
      Finset.card_range]
  have himg2 : (Kp.image f).card = ((Finset.range ω).erase c).card := by
    rw [himg, hcard, hcardE]
  exact Finset.eq_of_subset_of_card_le hsub himg2.ge

/-- Step 2: (P) implies perfect, by strong induction using Gasparian's
rank argument. Part (a) is `step2a_aux`; parts (b)–(d) build the
incidence family, and part (e) is `card_le_of_incid`. -/
private lemma ineq_implies_perfect {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hP : PerfIneq G) : IsPerfect G := by
  classical
  intro s
  let t : Finset V := s.toFinset
  have ht : (↑t : Set V) = s := Set.coe_toFinset s
  rw [← ht]
  have hle : ((G.induce (↑t : Set V)).cliqueNum : ℕ∞) ≤
      (G.induce (↑t : Set V)).chromaticNumber :=
    SimpleGraph.cliqueNum_le_chromaticNumber
  have hge : (G.induce (↑t : Set V)).chromaticNumber ≤
      ((G.induce (↑t : Set V)).cliqueNum : ℕ∞) := by
    suffices h : ∀ u : Finset V, u ⊆ t →
        (G.induce (↑u : Set V)).chromaticNumber ≤
          ((G.induce (↑u : Set V)).cliqueNum : ℕ∞) from
      h t Finset.Subset.rfl
    intro u
    induction u using Finset.strongInduction with
    | _ u ih =>
      intro _hut
      by_cases hcol : (G.induce (↑u : Set V)).Colorable
          (G.induce (↑u : Set V)).cliqueNum
      · exact (SimpleGraph.chromaticNumber_le_iff_colorable).mpr hcol
      · have ihCol : ∀ tt : Finset V, tt ⊂ u →
            (G.induce (↑tt : Set V)).Colorable
              (G.induce (↑tt : Set V)).cliqueNum := by
          intro tt htt
          exact (SimpleGraph.chromaticNumber_le_iff_colorable).mp
            (ih tt htt (Finset.Subset.trans htt.subset _hut))
        have hA := fun (S : Finset V) (hSS : S ⊆ u) (hne : S.Nonempty)
          (hind : G.IsIndepSet (↑S : Set V)) =>
          step2a_aux G u ihCol hcol S hSS hne hind
        have hne_u : u.Nonempty := by
          by_contra hempty
          have hempty2 : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
          subst hempty2
          apply hcol
          have hemptyC : (G.induce ((↑(∅ : Finset V)) : Set V)).Colorable
              0 := by
            refine ⟨SimpleGraph.Coloring.mk (fun x => False.elim ?_) ?_⟩
            · exact Finset.notMem_empty x.val (Finset.mem_coe.mp x.property)
            · intro v w hadj
              exact False.elim
                (Finset.notMem_empty v.val (Finset.mem_coe.mp v.property))
          have h0 : (G.induce ((↑(∅ : Finset V)) : Set V)).cliqueNum = 0 := by
            obtain ⟨K, hKsub, hKcard, _⟩ :=
              exists_maxClique_finset G (∅ : Finset V)
            have hKe : K = ∅ := Finset.eq_empty_of_forall_notMem
              (fun x hx => Finset.notMem_empty x (hKsub hx))
            have hK0 : K.card = 0 := by
              rw [hKe]
              rfl
            omega
          rw [h0]
          exact hemptyC
        obtain ⟨x0, hx0⟩ := hne_u
        have homega_pos : 1 ≤ (G.induce (↑u : Set V)).cliqueNum :=
          one_le_cliqueNum_of_mem G u x0 hx0
        have halpha_pos : 1 ≤ (G.induce (↑u : Set V)).indepNum :=
          one_le_indepNum_of_mem G u x0 hx0
        obtain ⟨A0, hA0sub, hA0card, hA0indep⟩ := exists_maxIndep_finset G u
        have hA0ne : A0.Nonempty := by
          rw [← Finset.card_pos, hA0card]
          omega
        have hcol_a : ∀ a ∈ A0, ∃ f : V → ℕ,
            (∀ v ∈ u \ {a}, f v < (G.induce (↑u : Set V)).cliqueNum) ∧
            ∀ x ∈ u \ {a}, ∀ y ∈ u \ {a}, G.Adj x y → f x ≠ f y := by
          intro a ha
          have hsub : u \ {a} ⊂ u := by
            rw [Finset.sdiff_singleton_eq_erase]
            exact Finset.erase_ssubset (hA0sub ha)
          have hkeep : (G.induce (↑(u \ {a}) : Set V)).cliqueNum =
              (G.induce (↑u : Set V)).cliqueNum := by
            have hsing : ({a} : Finset V) ⊆ u :=
              Finset.singleton_subset_iff.mpr (hA0sub ha)
            have hne1 : ({a} : Finset V).Nonempty :=
              Finset.singleton_nonempty a
            have hind1 : G.IsIndepSet ((↑({a} : Finset V)) : Set V) := by
              intro x hx y hy hne hadj
              simp only [Finset.coe_singleton] at hx hy
              subst hx
              subst hy
              exact absurd rfl hne
            exact hA ({a} : Finset V) hsing hne1 hind1
          have hrem := ihCol (u \ {a}) hsub
          rw [hkeep] at hrem
          exact fn_of_colorable G (u \ {a}) _ hrem
        choose g hgB hgS using hcol_a
        let A : Option (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum) →
            Finset V := fun j => match j with
          | none => A0
          | some (⟨a, ha⟩, i) =>
            (u \ {a}).filter (fun v => g a ha v = i.val)
        have hA_sub : ∀ j : Option
            (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum), A j ⊆ u := by
          intro j
          cases j with
          | none =>
            change A0 ⊆ u
            exact hA0sub
          | some p =>
            obtain ⟨⟨a, ha⟩, i⟩ := p
            change (u \ {a}).filter (fun v => g a ha v = i.val) ⊆ u
            exact (Finset.filter_subset _ _).trans Finset.sdiff_subset
        have hA_indep : ∀ j : Option
            (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum),
            G.IsIndepSet (↑(A j) : Set V) := by
          intro j
          cases j with
          | none =>
            change G.IsIndepSet (↑A0 : Set V)
            exact hA0indep
          | some p =>
            obtain ⟨⟨a, ha⟩, i⟩ := p
            change G.IsIndepSet
              (↑((u \ {a}).filter (fun v => g a ha v = i.val)) : Set V)
            intro x hx y hy hne hadj
            have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
            have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
            obtain ⟨hxmem, hxeq⟩ := hx'
            obtain ⟨hymem, hyeq⟩ := hy'
            have hne2 := hgS a ha x hxmem y hymem hadj
            rw [hxeq, hyeq] at hne2
            exact absurd rfl hne2
        have hKex : ∀ j : Option
            (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum), ∃ K : Finset V,
            K ⊆ u ∧ K.card = (G.induce (↑u : Set V)).cliqueNum ∧
            G.IsClique (↑K : Set V) ∧ Disjoint K (A j) := by
          intro j
          by_cases hj : (A j).Nonempty
          · obtain ⟨K', hK'sub, hK'card, hK'clique⟩ :=
              exists_maxClique_finset G (u \ A j)
            have hkeep : (G.induce (↑(u \ A j) : Set V)).cliqueNum =
                (G.induce (↑u : Set V)).cliqueNum :=
              hA (A j) (hA_sub j) hj (hA_indep j)
            rw [hkeep] at hK'card
            refine ⟨K', hK'sub.trans Finset.sdiff_subset, hK'card, hK'clique,
              ?_⟩
            rw [Finset.disjoint_left]
            intro x hxK hxA
            exact (Finset.mem_sdiff.mp (hK'sub hxK)).2 hxA
          · rw [Finset.not_nonempty_iff_eq_empty] at hj
            obtain ⟨K, hKsub, hKcard, hKclique⟩ := exists_maxClique_finset G u
            refine ⟨K, hKsub, hKcard, hKclique, ?_⟩
            rw [hj]
            exact Finset.disjoint_empty_right _
        choose K hKsub hKcard hKclique hKdisj using hKex
        have hdiag : ∀ j : Option
            (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum),
            (A j ∩ K j).card = 0 := by
          intro j
          have hdis : Disjoint (A j) (K j) := (hKdisj j).symm
          rw [Finset.disjoint_iff_inter_eq_empty] at hdis
          rw [hdis]
          rfl
        have hAnone : A none = A0 := rfl
        have hAsome : ∀ (a : V) (ha : a ∈ A0)
            (i : Fin (G.induce (↑u : Set V)).cliqueNum),
            A (some (⟨a, ha⟩, i)) =
              (u \ {a}).filter (fun v => g a ha v = i.val) := by
          intro a ha i
          rfl
        have hoff : ∀ j l : Option
            (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum),
            j ≠ l → (A j ∩ K l).card = 1 := by
          intro j l hne
          have hF1 : ∀ (a : V) (ha : a ∈ A0), a ∉ K l →
              ∀ i : Fin (G.induce (↑u : Set V)).cliqueNum,
                (A (some (⟨a, ha⟩, i)) ∩ K l).card = 1 := by
            intro a ha haK i
            rw [hAsome a ha i]
            have hsub : K l ⊆ u \ {a} := by
              intro v hvK
              rw [Finset.mem_sdiff]
              refine ⟨hKsub l hvK, ?_⟩
              intro hcon
              have heq : v = a := Finset.mem_singleton.mp hcon
              rw [heq] at hvK
              exact haK hvK
            have hb : ∀ v ∈ K l,
                g a ha v < (G.induce (↑u : Set V)).cliqueNum :=
              fun v hv => hgB a ha v (hsub hv)
            have hinj : Set.InjOn (g a ha) (↑(K l) : Set V) := by
              intro x1 hx1 x2 hx2 heq
              by_contra hne2
              have hadj : G.Adj x1 x2 := hKclique l hx1 hx2 hne2
              have hsep := hgS a ha x1 (hsub (Finset.mem_coe.mp hx1)) x2
                (hsub (Finset.mem_coe.mp hx2)) hadj
              exact hsep heq
            have himg := image_eq_range_of_injOn (g a ha) (K l)
              (G.induce (↑u : Set V)).cliqueNum (hKcard l) hb hinj
            have hmem : i.val ∈ (K l).image (g a ha) := by
              rw [himg]
              exact Finset.mem_range.mpr i.isLt
            have hfib :=
              filter_fiber_card_eq_one (g a ha) (K l) i.val hmem hinj
            have hinter :
                (u \ {a}).filter (fun v => g a ha v = i.val) ∩ K l =
                (K l).filter (fun v => g a ha v = i.val) := by
              ext v
              simp only [Finset.mem_inter, Finset.mem_filter]
              constructor
              · rintro ⟨⟨hvsub, hvf⟩, hvK⟩
                exact ⟨hvK, hvf⟩
              · rintro ⟨hvK, hvf⟩
                exact ⟨⟨hsub hvK, hvf⟩, hvK⟩
            rw [hinter]
            exact hfib
          have hF2 : ∀ (a : V) (ha : a ∈ A0), a ∈ K l → ∀ (c : ℕ),
              c < (G.induce (↑u : Set V)).cliqueNum →
              c ∉ ((K l).erase a).image (g a ha) →
              ∀ i : Fin (G.induce (↑u : Set V)).cliqueNum, i.val ≠ c →
                (A (some (⟨a, ha⟩, i)) ∩ K l).card = 1 := by
            intro a ha haK c hc hmiss i hne_i
            rw [hAsome a ha i]
            have hsub : (K l).erase a ⊆ u \ {a} := by
              intro v hv
              rw [Finset.mem_sdiff]
              have hvE := Finset.mem_erase.mp hv
              refine ⟨hKsub l hvE.2, ?_⟩
              intro hcon
              exact hvE.1 (Finset.mem_singleton.mp hcon)
            have hb : ∀ v ∈ (K l).erase a,
                g a ha v < (G.induce (↑u : Set V)).cliqueNum :=
              fun v hv => hgB a ha v (hsub hv)
            have hinj : Set.InjOn (g a ha) (↑((K l).erase a) : Set V) := by
              intro x1 hx1 x2 hx2 heq
              by_contra hne2
              have hx1K : x1 ∈ (↑(K l) : Set V) := Finset.mem_coe.mpr
                (Finset.erase_subset a (K l) (Finset.mem_coe.mp hx1))
              have hx2K : x2 ∈ (↑(K l) : Set V) := Finset.mem_coe.mpr
                (Finset.erase_subset a (K l) (Finset.mem_coe.mp hx2))
              have hadj : G.Adj x1 x2 := hKclique l hx1K hx2K hne2
              have hsep := hgS a ha x1 (hsub (Finset.mem_coe.mp hx1)) x2
                (hsub (Finset.mem_coe.mp hx2)) hadj
              exact hsep heq
            have hcardE : ((K l).erase a).card =
                (G.induce (↑u : Set V)).cliqueNum - 1 := by
              rw [Finset.card_erase_of_mem haK, hKcard l]
            have himg := image_eq_erase_range_of_injOn (g a ha) ((K l).erase a)
              (G.induce (↑u : Set V)).cliqueNum c hc hcardE hb hinj hmiss
            have hmem : i.val ∈ ((K l).erase a).image (g a ha) := by
              rw [himg, Finset.mem_erase, Finset.mem_range]
              exact ⟨hne_i, i.isLt⟩
            have hfib := filter_fiber_card_eq_one (g a ha) ((K l).erase a)
              i.val hmem hinj
            have hinter :
                (u \ {a}).filter (fun v => g a ha v = i.val) ∩ K l =
                ((K l).erase a).filter (fun v => g a ha v = i.val) := by
              ext v
              simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨⟨hvsub, hvf⟩, hvK⟩
                have hne3 : v ≠ a := by
                  intro heq2
                  exact (Finset.mem_sdiff.mp hvsub).2
                    (Finset.mem_singleton.mpr heq2)
                exact ⟨⟨hne3, hvK⟩, hvf⟩
              · rintro ⟨⟨hne3, hvK⟩, hvf⟩
                have hvsub : v ∈ u \ {a} := by
                  rw [Finset.mem_sdiff]
                  refine ⟨hKsub l hvK, ?_⟩
                  intro hcon
                  exact hne3 (Finset.mem_singleton.mp hcon)
                exact ⟨⟨hvsub, hvf⟩, hvK⟩
            rw [hinter]
            exact hfib
          by_cases hA0case : (A0 ∩ K l).Nonempty
          · have hcard01 : (A0 ∩ K l).card = 1 := by
              have h1 := card_inter_clique_indep_le_one G A0 (K l)
                hA0indep (hKclique l)
              have hpos := Finset.card_pos.mpr hA0case
              omega
            obtain ⟨astar, hsingle⟩ := Finset.card_eq_one.mp hcard01
            have haK : astar ∈ K l := by
              have hmem : astar ∈ A0 ∩ K l := by
                rw [hsingle]
                exact Finset.mem_singleton_self astar
              exact (Finset.mem_inter.mp hmem).2
            cases l with
            | none =>
              have hfalse : False := by
                have h1 : (A none ∩ K none).card = 1 := by
                  rw [hAnone, hsingle, Finset.card_singleton]
                have h0 := hdiag none
                omega
              exact False.elim hfalse
            | some p =>
              obtain ⟨⟨ap, hap⟩, ip⟩ := p
              have hap_eq : astar = ap := by
                by_contra hne_ap
                have hne_ap2 : ap ≠ astar := fun h => hne_ap h.symm
                have hanot : ap ∉ K (some (⟨ap, hap⟩, ip)) := by
                  intro hmemK
                  have hmemI : ap ∈ A0 ∩ K (some (⟨ap, hap⟩, ip)) :=
                    Finset.mem_inter.mpr ⟨hap, hmemK⟩
                  rw [hsingle] at hmemI
                  exact hne_ap2 (Finset.mem_singleton.mp hmemI)
                have h1 := hF1 ap hap hanot ip
                have h0 := hdiag (some (⟨ap, hap⟩, ip))
                omega
              subst hap_eq
              cases j with
              | none =>
                rw [hAnone, hsingle, Finset.card_singleton]
              | some q =>
                obtain ⟨⟨a, ha⟩, i⟩ := q
                by_cases heq_a : astar = a
                · subst heq_a
                  have hne_ip : i.val ≠ ip.val := by
                    intro heq_v
                    have heq_i : i = ip := Fin.val_injective heq_v
                    apply hne
                    rw [heq_i]
                  have hmiss : ip.val ∉ ((K (some (⟨astar, hap⟩, ip))).erase
                      astar).image (g astar ha) := by
                    intro hcon
                    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hcon
                    have hvA : v ∈ A (some (⟨astar, hap⟩, ip)) := by
                      rw [hAsome astar hap ip]
                      rw [Finset.mem_filter]
                      have hvE := Finset.mem_erase.mp hv
                      refine ⟨?_, hfv⟩
                      rw [Finset.mem_sdiff]
                      refine ⟨hKsub _ hvE.2, ?_⟩
                      intro hcon2
                      exact hvE.1 (Finset.mem_singleton.mp hcon2)
                    have hvK : v ∈ K (some (⟨astar, hap⟩, ip)) :=
                      Finset.erase_subset astar _ hv
                    have hmemI : v ∈ A (some (⟨astar, hap⟩, ip)) ∩
                        K (some (⟨astar, hap⟩, ip)) :=
                      Finset.mem_inter.mpr ⟨hvA, hvK⟩
                    have hpos := Finset.card_pos.mpr ⟨v, hmemI⟩
                    have h0 := hdiag (some (⟨astar, hap⟩, ip))
                    omega
                  exact hF2 astar ha haK ip.val ip.isLt hmiss i hne_ip
                · have heq_a2 : a ≠ astar := fun h => heq_a h.symm
                  have hanot : a ∉ K (some (⟨astar, hap⟩, ip)) := by
                    intro hmemK
                    have hmemI : a ∈ A0 ∩ K (some (⟨astar, hap⟩, ip)) :=
                      Finset.mem_inter.mpr ⟨ha, hmemK⟩
                    rw [hsingle] at hmemI
                    exact heq_a2 (Finset.mem_singleton.mp hmemI)
                  exact hF1 a ha hanot i
          · have hempty : A0 ∩ K l = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hA0case
            cases l with
            | none =>
              cases j with
              | none =>
                exact absurd rfl hne
              | some q =>
                obtain ⟨⟨a, ha⟩, i⟩ := q
                have hanot : a ∉ K none := by
                  intro hmemK
                  have hmemI : a ∈ A0 ∩ K none :=
                    Finset.mem_inter.mpr ⟨ha, hmemK⟩
                  rw [hempty] at hmemI
                  exact Finset.notMem_empty a hmemI
                exact hF1 a ha hanot i
            | some p =>
              obtain ⟨⟨ap, hap⟩, ip⟩ := p
              have hanot : ap ∉ K (some (⟨ap, hap⟩, ip)) := by
                intro hmemK
                have hmemI : ap ∈ A0 ∩ K (some (⟨ap, hap⟩, ip)) :=
                  Finset.mem_inter.mpr ⟨hap, hmemK⟩
                rw [hempty] at hmemI
                exact Finset.notMem_empty ap hmemI
              have hfalse : False := by
                have h1 := hF1 ap hap hanot ip
                have h0 := hdiag (some (⟨ap, hap⟩, ip))
                omega
              exact False.elim hfalse
        have hJcard : Fintype.card
            (Option (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum)) =
            (G.induce (↑u : Set V)).indepNum *
              (G.induce (↑u : Set V)).cliqueNum + 1 := by
          rw [Fintype.card_option, Fintype.card_prod, Fintype.card_coe,
            Fintype.card_fin, hA0card]
        have hN2 : 2 ≤ Fintype.card
            (Option (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum)) := by
          rw [hJcard]
          have hmul : 1 ≤ (G.induce (↑u : Set V)).indepNum *
              (G.induce (↑u : Set V)).cliqueNum := by
            simpa using Nat.mul_le_mul halpha_pos homega_pos
          omega
        have hle_rank : Fintype.card
            (Option (↥A0 × Fin (G.induce (↑u : Set V)).cliqueNum)) ≤
            u.card :=
          card_le_of_incid u _ A K hA_sub hN2 hdiag hoff
        have hPle : u.card ≤ (G.induce (↑u : Set V)).indepNum *
            (G.induce (↑u : Set V)).cliqueNum := hP u
        rw [hJcard] at hle_rank
        have hfalse : False := by omega
        exact False.elim hfalse
  exact le_antisymm hge hle

/--
Weak perfect graph theorem without decidable equality: `G` perfect iff `Gᶜ` perfect.
General version of `lovasz_weak_perfect_graph`; the `DecidableEq` instance needed by
the internal finset argument is obtained locally via `classical`.
-/
theorem lovasz_weak_perfect_graph_general
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) : IsPerfect G ↔ IsPerfect Gᶜ := by
  classical
  constructor
  · intro h
    have hP : PerfIneq G := perfect_implies_ineq G h
    have hPc : PerfIneq Gᶜ := (ineq_compl_iff G).mp hP
    exact ineq_implies_perfect Gᶜ hPc
  · intro h
    have hP : PerfIneq Gᶜ := perfect_implies_ineq Gᶜ h
    have hPc : PerfIneq G := (ineq_compl_iff G).mpr hP
    exact ineq_implies_perfect G hPc

set_option linter.unusedDecidableInType false in
/--
Weak perfect graph theorem: `G` perfect iff `Gᶜ` perfect.
Source: L. Lovasz, "Normal hypergraphs and the perfect graph conjecture", Discrete Math. 2 (1972),
253-267, DOI 10.1016/0012-365X(72)90006-4.

Proves `Wanted` entry `lovasz_weak_perfect_graph`.
-/
theorem lovasz_weak_perfect_graph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsPerfect G ↔ IsPerfect Gᶜ :=
  lovasz_weak_perfect_graph_general G

end MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted
end

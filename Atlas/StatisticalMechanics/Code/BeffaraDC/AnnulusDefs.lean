/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.TwoDim.Crossings

open Set
open StatMech.Lattice
open SimpleGraph

namespace StatMech

namespace BeffaraDC







def annulus (n N : ℕ) : Set (Site 2) := box 2 N \ box 2 n

@[simp]
theorem mem_annulus {n N : ℕ} {x : Site 2} :
    x ∈ annulus n N ↔ x ∈ box 2 N ∧ x ∉ box 2 n := Iff.rfl


theorem annulus_subset_box (n N : ℕ) : annulus n N ⊆ box 2 N := Set.diff_subset



theorem annulus_disjoint_inner (n N : ℕ) : Disjoint (annulus n N) (box 2 n) :=
  Set.disjoint_sdiff_left


theorem annulus_finite (n N : ℕ) : (annulus n N).Finite :=
  (box_finite 2 N).subset (annulus_subset_box n N)



theorem annulus_empty_of_le (N : ℕ) : annulus N N = ∅ := by
  simp [annulus]





theorem openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω') :
    openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle




def IsAnnulusCircuit (ω : ConfigSpace (Sym2 (Site 2))) (n N : ℕ)
    {x : Site 2} (w : (openSubgraph 2 ω).Walk x x) : Prop :=
  w.IsCircuit ∧ ∀ y ∈ w.support, y ∈ annulus n N

theorem IsAnnulusCircuit.isCircuit {ω : ConfigSpace (Sym2 (Site 2))} {n N : ℕ}
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x} (h : IsAnnulusCircuit ω n N w) :
    w.IsCircuit := h.1



theorem IsAnnulusCircuit.support_subset_box {ω : ConfigSpace (Sym2 (Site 2))}
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : ∀ y ∈ w.support, y ∈ box 2 N :=
  fun y hy => (h.2 y hy).1



theorem IsAnnulusCircuit.support_avoids_inner {ω : ConfigSpace (Sym2 (Site 2))}
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : ∀ y ∈ w.support, y ∉ box 2 n :=
  fun y hy => (h.2 y hy).2


theorem IsAnnulusCircuit.base_mem {ω : ConfigSpace (Sym2 (Site 2))} {n N : ℕ}
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : x ∈ annulus n N :=
  h.2 x (Walk.start_mem_support w)













def Separates (C : Set (Site 2)) (n N : ℕ) : Prop :=
  ∀ (u v : Site 2), u ∈ box 2 n → v ∉ box 2 N →
    ∀ (p : (hypercubicLattice 2).Walk u v), ∃ z ∈ p.support, z ∈ C


theorem Separates.mono {C C' : Set (Site 2)} (hCC' : C ⊆ C') {n N : ℕ}
    (h : Separates C n N) : Separates C' n N := by
  intro u v hu hv p
  obtain ⟨z, hz, hzC⟩ := h u v hu hv p
  exact ⟨z, hz, hCC' hzC⟩














def AnnulusEvent (ω : ConfigSpace (Sym2 (Site 2))) (n N M : ℕ) : Prop :=
  ∃ (x : Site 2) (w : (openSubgraph 2 ω).Walk x x),
    IsAnnulusCircuit ω n N w ∧
    Separates {z | z ∈ w.support} n N ∧
    ∃ y : Site 2, y ∈ box 2 M ∧ y ∉ box 2 (M - 1) ∧ Connected 2 ω x y


def annulusEvent (n N M : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | AnnulusEvent ω n N M}

@[simp]
theorem mem_annulusEvent {n N M : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusEvent n N M ↔ AnnulusEvent ω n N M := Iff.rfl









theorem mapLe_isCircuit {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x} (hc : w.IsCircuit) :
    (w.mapLe (openSubgraph_mono h)).IsCircuit := by
  rw [Walk.isCircuit_def] at hc ⊢
  obtain ⟨ht, hne⟩ := hc
  refine ⟨?_, ?_⟩
  · show (Walk.map (Hom.ofLE (openSubgraph_mono h)) w).IsTrail
    rw [SimpleGraph.Walk.map_isTrail_iff_of_injective (fun _ _ hab => hab)]
    exact ht
  · show Walk.map (Hom.ofLE (openSubgraph_mono h)) w ≠ Walk.nil
    intro hcon
    apply hne
    cases w with
    | nil => rfl
    | cons hadj rest => simp [Walk.map] at hcon



theorem mapLe_support {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {x : Site 2} (w : (openSubgraph 2 ω).Walk x x) :
    (w.mapLe (openSubgraph_mono h)).support = w.support := by
  show (Walk.map (Hom.ofLE (openSubgraph_mono h)) w).support = w.support
  rw [Walk.support_map]
  apply List.map_id''
  intro _; rfl


theorem IsAnnulusCircuit.mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (hw : IsAnnulusCircuit ω n N w) :
    IsAnnulusCircuit ω' n N (w.mapLe (openSubgraph_mono h)) := by
  refine ⟨mapLe_isCircuit h hw.1, ?_⟩
  intro y hy
  rw [mapLe_support h w] at hy
  exact hw.2 y hy



theorem annulusEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {n N M : ℕ} (hω : ω ∈ annulusEvent n N M) : ω' ∈ annulusEvent n N M := by
  obtain ⟨x, w, hcirc, hsep, y, hyM, hyM', hconn⟩ := hω
  refine ⟨x, w.mapLe (openSubgraph_mono h), hcirc.mono h, ?_, y, hyM, hyM', ?_⟩
  · rw [show {z | z ∈ (w.mapLe (openSubgraph_mono h)).support} = {z | z ∈ w.support}
        from by rw [mapLe_support h w]]
    exact hsep
  · exact hconn.mono (openSubgraph_mono h)








def diagReflFun (x : Site 2) : Site 2 := ![x 1, x 0]

@[simp] theorem diagReflFun_apply (a b : ℤ) : diagReflFun ![a, b] = ![b, a] := by
  funext i; fin_cases i <;> simp [diagReflFun]


theorem diagReflFun_involutive : Function.Involutive diagReflFun := by
  intro x; funext i; fin_cases i <;> simp [diagReflFun]


def diagReflEquiv : Site 2 ≃ Site 2 :=
  Function.Involutive.toPerm diagReflFun diagReflFun_involutive

@[simp] theorem diagReflEquiv_apply (x : Site 2) : diagReflEquiv x = diagReflFun x := rfl
@[simp] theorem diagReflEquiv_symm_apply (x : Site 2) :
    diagReflEquiv.symm x = diagReflFun x := rfl



theorem diagRefl_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (diagReflFun x) (diagReflFun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [diagReflFun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Nat.add_comm]



def diagReflIso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨diagReflEquiv, fun {x y} => diagRefl_adj x y⟩

@[simp] theorem diagReflIso_apply (x : Site 2) : diagReflIso x = diagReflFun x := rfl





abbrev LatticePath (u v : Site 2) := (hypercubicLattice 2).Walk u v




def IsSymmetricPair {u₁ v₁ u₂ v₂ : Site 2}
    (γ₁ : LatticePath u₁ v₁) (γ₂ : LatticePath u₂ v₂) : Prop :=
  diagReflFun '' {z | z ∈ γ₁.support} = {z | z ∈ γ₂.support}



theorem IsSymmetricPair.symm {u₁ v₁ u₂ v₂ : Site 2}
    {γ₁ : LatticePath u₁ v₁} {γ₂ : LatticePath u₂ v₂}
    (h : IsSymmetricPair γ₁ γ₂) :
    diagReflFun '' {z | z ∈ γ₂.support} = {z | z ∈ γ₁.support} := by
  rw [← h, ← Set.image_comp, diagReflFun_involutive.comp_self, Set.image_id]








structure SymmetricDomain where
  
  u₁ : Site 2
  
  v₁ : Site 2
  
  u₂ : Site 2
  
  v₂ : Site 2
  
  γ₁ : LatticePath u₁ v₁
  
  γ₂ : LatticePath u₂ v₂
  
  isSymm : IsSymmetricPair γ₁ γ₂
  
  G : Set (Site 2)
  
  finite : G.Finite
  
  γ₁_subset : {z | z ∈ γ₁.support} ⊆ G
  
  γ₂_subset : {z | z ∈ γ₂.support} ⊆ G
  
  G_symm : diagReflFun '' G = G

namespace SymmetricDomain

variable (D : SymmetricDomain)



def wired : Set (Site 2) :=
  {z | z ∈ D.γ₁.support} ∪ {z | z ∈ D.γ₂.support}



def free : Set (Site 2) := D.G \ D.wired


theorem wired_subset : D.wired ⊆ D.G := by
  rintro z (hz | hz)
  · exact D.γ₁_subset hz
  · exact D.γ₂_subset hz


theorem free_subset : D.free ⊆ D.G := Set.diff_subset


theorem wired_union_free : D.wired ∪ D.free = D.G := by
  rw [free, Set.union_diff_cancel D.wired_subset]

theorem wired_disjoint_free : Disjoint D.wired D.free :=
  Set.disjoint_sdiff_right


theorem wired_finite : D.wired.Finite := D.finite.subset D.wired_subset



theorem wired_symm : diagReflFun '' D.wired = D.wired := by
  rw [wired, Set.image_union, D.isSymm, D.isSymm.symm, Set.union_comm]







def Connected (D : SymmetricDomain) (ω : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ∃ (x : {z | z ∈ D.γ₁.support}) (y : {z | z ∈ D.γ₂.support}),
    ConnectedWithin 2 ω D.G
      ⟨(x : Site 2), D.γ₁_subset x.2⟩ ⟨(y : Site 2), D.γ₂_subset y.2⟩


def connectionEvent (D : SymmetricDomain) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | D.Connected ω}

@[simp]
theorem mem_connectionEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ D.connectionEvent ↔ D.Connected ω := Iff.rfl



theorem Connected.connected {D : SymmetricDomain} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : D.Connected ω) :
    ∃ x y : Site 2, x ∈ {z | z ∈ D.γ₁.support} ∧ y ∈ {z | z ∈ D.γ₂.support} ∧
      StatMech.Lattice.Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩



theorem connectionEvent_increasing {D : SymmetricDomain}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ D.connectionEvent) : ω' ∈ D.connectionEvent := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono h hxy⟩

end SymmetricDomain

end BeffaraDC

end StatMech

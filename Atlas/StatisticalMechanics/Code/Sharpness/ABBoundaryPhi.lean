/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABBoundaryProfile
import Code.Sharpness.ABInfiniteGhost
import Code.Sharpness.BkCriterionInfinite
import Code.Sharpness.TildeBc
import Code.Percolation.DctItem2
import Mathlib.Data.Finset.Preimage

open Filter Finset Set SimpleGraph Topology
open scoped NNReal

namespace StatMech
namespace Sharpness

open ConfigSpace Lattice
open StatMech.Percolation



theorem abb_probV_eq_section {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → Real) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : StatMech.DependsOn A (F : Set E)) :
    probV p A = probV (fun e : F ↦ p e)
      (ih_section A F) := by
  let mu := inhomBernoulliProductMeasure (fun e ↦ (p e).toNNReal)
    (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e))
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F hA
  calc
    probV p A = mu.real A :=
      (inhom_real_eq_probV_of_mem p hp0 hp1 A).symm
    _ = mu.real (MeasureTheory.cylinder F (ih_section A F)) :=
      congrArg mu.real hAcyl
    _ = (inhomBernoulliProductMeasure
          (fun e : F ↦ (p e).toNNReal)
          (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e))).real
          (ih_section A F) :=
      inhom_realProb_cylinder (fun e ↦ (p e).toNNReal)
        (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e)) F _
    _ = probV (fun e : F ↦ p e) (ih_section A F) :=
      inhom_real_eq_probV_of_mem (fun e : F ↦ p e)
        (fun e ↦ hp0 e) (fun e ↦ hp1 e) _



theorem abb_probV_eq_of_agreeOn {E : Type*} [Fintype E] [DecidableEq E]
    (p q : E → Real)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : StatMech.DependsOn A (F : Set E))
    (hpq : ∀ e ∈ F, p e = q e) :
    probV p A = probV q A := by
  rw [abb_probV_eq_section p hp0 hp1 A F hA,
    abb_probV_eq_section q hq0 hq1 A F hA]
  congr 1
  funext e
  exact hpq e e.property



theorem abb_internal_openSub_adj {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W)
    (eta : ConfigSpace (abigInternalEdges T)) (a b : T) :
    (openSub (G.induce (T : Set W))
      (cfgEquiv (abigInternalEdgeEquiv T) eta)).Adj a b ↔
      (openSub G (ih_fill (abigInternalEdges T) eta)).Adj (a : W) (b : W) := by
  have he : s((a : W), (b : W)) ∈ abigInternalEdges T :=
    mem_abigInternalEdges.mpr ⟨a, a.property, b, b.property, rfl⟩
  have hcoord : abigInternalEdgeEquiv T s(a, b) =
      (⟨s((a : W), (b : W)), he⟩ : abigInternalEdges T) := by
    apply Subtype.ext
    exact abigInternalEdgeEquiv_mk T a b
  simp only [openSub, SimpleGraph.induce_adj, cfgEquiv_apply]
  rw [ih_fill, dif_pos he]
  constructor
  · rintro ⟨hG, heta⟩
    exact ⟨hG, hcoord ▸ heta⟩
  · rintro ⟨hG, heta⟩
    exact ⟨hG, hcoord.symm ▸ heta⟩



theorem abb_preimage_connEvent_induce {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W) (o x : T) :
    (cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹'
        connEvent (G.induce (T : Set W)) Set.univ o {x} =
      ih_section (connEvent G (T : Set W) (o : W) {(x : W)})
        (abigInternalEdges T) := by
  ext eta
  change ConnToSet (G.induce (T : Set W))
      (cfgEquiv (abigInternalEdgeEquiv T) eta) Set.univ o {x} ↔
    ConnToSet G (ih_fill (abigInternalEdges T) eta)
      (T : Set W) (o : W) {(x : W)}
  constructor
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    let f :
        ((openSub (G.induce (T : Set W))
          (cfgEquiv (abigInternalEdgeEquiv T) eta)).induce Set.univ) →g
        ((openSub G (ih_fill (abigInternalEdges T) eta)).induce
          (T : Set W)) :=
      { toFun := fun z ↦ ⟨(z : T), z.1.property⟩
        map_rel' := fun {u v} huv ↦
          (abb_internal_openSub_adj G T eta u v).mp huv }
    exact ⟨o.property, (x : W), x.property, rfl, hconn.map f⟩
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = (x : W) := Set.mem_singleton_iff.mp hy
    subst y
    let f :
        ((openSub G (ih_fill (abigInternalEdges T) eta)).induce
          (T : Set W)) →g
        ((openSub (G.induce (T : Set W))
          (cfgEquiv (abigInternalEdgeEquiv T) eta)).induce Set.univ) :=
      { toFun := fun z ↦ ⟨(z : T), Set.mem_univ _⟩
        map_rel' := fun {u v} huv ↦
          (abb_internal_openSub_adj G T eta u v).mpr huv }
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl, hconn.map f⟩



theorem abb_probV_connEvent_eq_induce {W : Type*}
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (p : Sym2 W → Real)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (T : Finset W) (o x : T) :
    probV p (connEvent G (T : Set W) (o : W) {(x : W)}) =
      probV (fun e : Sym2 T ↦ p (Sym2.map Subtype.val e))
        (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
  let F := abigInternalEdges T
  let A := connEvent G (T : Set W) (o : W) {(x : W)}
  let AI := connEvent (G.induce (T : Set W)) Set.univ o {x}
  let q : Sym2 T → Real := fun e ↦ p (Sym2.map Subtype.val e)
  have hdep : StatMech.DependsOn A (F : Set (Sym2 W)) :=
    abig_connEvent_dependsOn G T (o : W) (x : W)
  rw [abb_probV_eq_section p hp0 hp1 A F hdep]
  symm
  calc
    probV q AI =
        probV (fun y : F ↦ q ((abigInternalEdgeEquiv T).symm y))
          ((cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹' AI) :=
      abfs_probV_transfer (abigInternalEdgeEquiv T) q AI
    _ = probV (fun e : F ↦ p e) (ih_section A F) := by
      have hevent :
          (cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹' AI = ih_section A F := by
        exact abb_preimage_connEvent_induce G T o x
      rw [hevent]
      congr 1
      funext e
      apply congrArg p
      exact congrArg Subtype.val ((abigInternalEdgeEquiv T).apply_symm_apply e)



theorem abb_hom_real_eq_probV {E : Type*} [Fintype E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1) (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure (fun _ : E ↦ p) (fun _ ↦ hp)).real A =
      probV (fun _ : E ↦ (p : Real)) A := by
  simpa using
    (inhom_real_eq_probV_of_mem (fun _ : E ↦ (p : Real))
      (fun _ ↦ p.coe_nonneg) (fun _ ↦ NNReal.coe_le_one.mpr hp) A)



theorem abb_probV_section_const_eq_induce {W : Type*} [DecidableEq W]
    (p : Real) (G : SimpleGraph W) (T : Finset W) (o x : T) :
    probV (fun _ : abigInternalEdges T ↦ p)
        (ih_section (connEvent G (T : Set W) (o : W) {(x : W)})
          (abigInternalEdges T)) =
      probV (fun _ : Sym2 T ↦ p)
        (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
  have ht := abfs_probV_transfer (abigInternalEdgeEquiv T)
    (fun _ : Sym2 T ↦ p)
    (connEvent (G.induce (T : Set W)) Set.univ o {x})
  rw [abb_preimage_connEvent_induce G T o x] at ht
  simpa only using ht.symm


noncomputable def abbEdgeEquiv {V U : Type*} (sigma : V ≃ U) :
    Sym2 V ≃ Sym2 U :=
  StatMech.Lattice.sym2Congr sigma

@[simp] theorem abbEdgeEquiv_mk {V U : Type*} (sigma : V ≃ U)
    (x y : V) :
    abbEdgeEquiv sigma s(x, y) = s(sigma x, sigma y) := by
  simp [abbEdgeEquiv, StatMech.Lattice.sym2Congr_mk]


theorem abb_openSub_adj_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (omega : ConfigSpace (Sym2 U)) (x y : V) :
    (openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).Adj x y ↔
      (openSub H omega).Adj (sigma x) (sigma y) := by
  simp only [openSub, cfgEquiv_apply, abbEdgeEquiv_mk]
  exact and_congr (hG x y) Iff.rfl


theorem abb_connWithin_univ_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (omega : ConfigSpace (Sym2 U)) (x y : V) :
    ConnWithin G (cfgEquiv (abbEdgeEquiv sigma) omega) Set.univ
        ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ ↔
      ConnWithin H omega Set.univ
        ⟨sigma x, Set.mem_univ _⟩ ⟨sigma y, Set.mem_univ _⟩ := by
  constructor
  · intro hconn
    let f :
        ((openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).induce
          Set.univ) →g
        ((openSub H omega).induce Set.univ) :=
      { toFun := fun z ↦ ⟨sigma z, Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦
          (abb_openSub_adj_relabel G H sigma hG omega a b).mp hab }
    exact hconn.map f
  · intro hconn
    let f :
        ((openSub H omega).induce Set.univ) →g
        ((openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).induce
          Set.univ) :=
      { toFun := fun z ↦ ⟨sigma.symm z, Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦ by
          apply (abb_openSub_adj_relabel G H sigma hG omega
            (sigma.symm a) (sigma.symm b)).mpr
          simpa using hab }
    convert hconn.map f using 1 <;> simp [f]



theorem abb_preimage_connEvent_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (o x : V) :
    (cfgEquiv (abbEdgeEquiv sigma)) ⁻¹'
        connEvent G Set.univ o {x} =
      connEvent H Set.univ (sigma o) {sigma x} := by
  ext omega
  change ConnToSet G (cfgEquiv (abbEdgeEquiv sigma) omega)
      Set.univ o {x} ↔ ConnToSet H omega Set.univ (sigma o) {sigma x}
  constructor
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨Set.mem_univ _, sigma x, Set.mem_univ _, rfl,
      (abb_connWithin_univ_relabel G H sigma hG omega o x).mp hconn⟩
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = sigma x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl,
      (abb_connWithin_univ_relabel G H sigma hG omega o x).mpr hconn⟩



theorem abb_probV_connEvent_relabel {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (p : Sym2 V → Real) (o x : V) :
    probV p (connEvent G Set.univ o {x}) =
      probV (fun e : Sym2 U ↦ p ((abbEdgeEquiv sigma).symm e))
        (connEvent H Set.univ (sigma o) {sigma x}) := by
  rw [← abb_preimage_connEvent_relabel G H sigma hG o x]
  exact abfs_probV_transfer (abbEdgeEquiv sigma) p _



theorem abb_connEvent_univ_dependsOn_edges {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset (Sym2 V))
    (hD : ∀ a b, G.Adj a b → s(a, b) ∈ D) (o x : V) :
    StatMech.DependsOn (connEvent G Set.univ o {x})
      (D : Set (Sym2 V)) := by
  intro omega omega' hagree
  have hforward : ∀ {eta eta' : ConfigSpace (Sym2 V)},
      (∀ e ∈ D, eta' e = eta e) →
      eta ∈ connEvent G Set.univ o {x} →
      eta' ∈ connEvent G Set.univ o {x} := by
    intro eta eta' heq hconn
    rcases hconn with ⟨_, y, _, hy, hreach⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    let f : ((openSub G eta).induce Set.univ) →g
        ((openSub G eta').induce Set.univ) :=
      { toFun := fun z ↦ ⟨(z : V), Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦ by
          refine ⟨hab.1, ?_⟩
          have hopen : eta' s((a : V), (b : V)) = true := by
            rw [heq s((a : V), (b : V))
              (hD (a : V) (b : V) hab.1)]
            exact hab.2
          simpa using hopen }
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl, hreach.map f⟩
  constructor
  · exact hforward hagree
  · exact hforward (fun e he ↦ (hagree e he).symm)


noncomputable def abbPhysicalSurface (d n : Nat)
    (S : Finset (Option (sctBox d n))) : Finset (sctBox d n) :=
  S.preimage some (by
    intro x hx y hy hxy
    exact Option.some.inj hxy)

@[simp] theorem mem_abbPhysicalSurface_iff {d n : Nat}
    {S : Finset (Option (sctBox d n))} {x : sctBox d n} :
    x ∈ abbPhysicalSurface d n S ↔ some x ∈ S := by
  simp [abbPhysicalSurface]


noncomputable def abbSiteSurface (d n : Nat)
    (S : Finset (Option (sctBox d n))) : Finset (Site d) :=
  (abbPhysicalSurface d n S).image Subtype.val

@[simp] theorem mem_abbSiteSurface_iff {d n : Nat}
    {S : Finset (Option (sctBox d n))} {x : Site d} :
    x ∈ abbSiteSurface d n S ↔
      ∃ hx : x ∈ box d n, some (⟨x, hx⟩ : sctBox d n) ∈ S := by
  classical
  constructor
  · rw [abbSiteSurface, Finset.mem_image]
    rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_abbPhysicalSurface_iff.mp hy⟩
  · rintro ⟨hx, hS⟩
    rw [abbSiteSurface, Finset.mem_image]
    exact ⟨⟨x, hx⟩, mem_abbPhysicalSurface_iff.mpr hS, rfl⟩


theorem abb_surface_eq_some_of_occurs {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) {z : Option (sctBox d n)} (hz : z ∈ S) :
    ∃ x, z = some x := by
  have hdisj := mpi_surfaceEvent_nonempty_disjoint
    (withGhost (sctBoxGraph d n)) (abbTarget d n) S hocc
  rcases z with _ | x
  · exact False.elim
      (Set.disjoint_left.mp hdisj (by simpa using hz) (none_mem_abbTarget d n))
  · exact ⟨x, rfl⟩



noncomputable def abbSurfaceValue {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (z : S) : sctBox d n :=
  Classical.choose (abb_surface_eq_some_of_occurs hocc z.property)

theorem abbSurfaceValue_spec {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (z : S) :
    (z : Option (sctBox d n)) = some (abbSurfaceValue hocc z) :=
  Classical.choose_spec (abb_surface_eq_some_of_occurs hocc z.property)



noncomputable def abbSurfaceEquiv {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    S ≃ abbPhysicalSurface d n S where
  toFun z := ⟨abbSurfaceValue hocc z, by
    apply mem_abbPhysicalSurface_iff.mpr
    rw [← abbSurfaceValue_spec hocc z]
    exact z.property⟩
  invFun x := ⟨some (x : sctBox d n),
    mem_abbPhysicalSurface_iff.mp x.property⟩
  left_inv z := by
    apply Subtype.ext
    exact (abbSurfaceValue_spec hocc z).symm
  right_inv x := by
    apply Subtype.ext
    exact Option.some.inj (abbSurfaceValue_spec hocc
      ⟨some (x : sctBox d n),
        mem_abbPhysicalSurface_iff.mp x.property⟩).symm

@[simp] theorem abbSurfaceEquiv_mk_some {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (x : sctBox d n) (hx : some x ∈ S) :
    abbSurfaceEquiv hocc ⟨some x, hx⟩ =
      (⟨x, mem_abbPhysicalSurface_iff.mpr hx⟩ : abbPhysicalSurface d n S) := by
  apply Subtype.ext
  exact Option.some.inj (abbSurfaceValue_spec hocc ⟨some x, hx⟩).symm

@[simp] theorem abbSurfaceEquiv_symm_apply {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (x : abbPhysicalSurface d n S) :
    (abbSurfaceEquiv hocc).symm x =
      (⟨some (x : sctBox d n),
        mem_abbPhysicalSurface_iff.mp x.property⟩ : S) := rfl



noncomputable def abbSiteSurfaceEquiv (d n : Nat)
    (S : Finset (Option (sctBox d n))) :
    abbPhysicalSurface d n S ≃ abbSiteSurface d n S :=
  Equiv.ofBijective
    (fun x ↦ ⟨((x : sctBox d n) : Site d), by
      rw [abbSiteSurface, Finset.mem_image]
      exact ⟨(x : sctBox d n), x.property, rfl⟩⟩)
    ⟨by
      intro x y hxy
      have hsite : ((x : sctBox d n) : Site d) =
          ((y : sctBox d n) : Site d) :=
        congrArg (fun z : abbSiteSurface d n S ↦ (z : Site d)) hxy
      apply Subtype.ext
      exact Subtype.ext hsite,
    by
      rintro ⟨z, hz⟩
      rw [abbSiteSurface, Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨⟨x, hx⟩, rfl⟩⟩

@[simp] theorem abbSiteSurfaceEquiv_apply (d n : Nat)
    (S : Finset (Option (sctBox d n)))
    (x : abbPhysicalSurface d n S) :
    ((abbSiteSurfaceEquiv d n S x : abbSiteSurface d n S) : Site d) =
      ((x : sctBox d n) : Site d) := rfl



theorem abbSurfaceEquiv_adj {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) (x y : S) :
    ((withGhost (sctBoxGraph d n)).induce (S : Set _)).Adj x y ↔
      ((sctBoxGraph d n).induce
        (abbPhysicalSurface d n S : Set _)).Adj
          (abbSurfaceEquiv hocc x) (abbSurfaceEquiv hocc y) := by
  have hx := abbSurfaceValue_spec hocc x
  have hy := abbSurfaceValue_spec hocc y
  simp only [SimpleGraph.induce_adj]
  rw [hx, hy]
  simp only [withGhost, Option.some.injEq]
  change (sctBoxGraph d n).Adj (abbSurfaceValue hocc x)
      (abbSurfaceValue hocc y) ↔
    (sctBoxGraph d n).Adj (abbSurfaceValue hocc x)
      (abbSurfaceValue hocc y)
  rfl



theorem abbSiteSurfaceEquiv_adj {d n : Nat}
    (S : Finset (Option (sctBox d n)))
    (x y : abbPhysicalSurface d n S) :
    ((sctBoxGraph d n).induce
      (abbPhysicalSurface d n S : Set _)).Adj x y ↔
      ((hypercubicLattice d).induce
        (abbSiteSurface d n S : Set _)).Adj
          (abbSiteSurfaceEquiv d n S x) (abbSiteSurfaceEquiv d n S y) := by
  simp [sctBoxGraph]



theorem abbParams_some_some (d n : Nat) (beta h : Real)
    (x y : sctBox d n) :
    abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
        s(some x, some y) =
      if (sctBoxGraph d n).Adj x y then pBeta 1 beta else 0 := by
  by_cases hxy : (sctBoxGraph d n).Adj x y
  · have he : s(x, y) ∈ (sctBoxGraph d n).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hxy
    simp [abfaParams, abpdBetaFieldParams, paramOn,
      FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
      abbCoupling, hxy, he]
  · have he : s(x, y) ∉ (sctBoxGraph d n).edgeFinset := fun h ↦
      hxy (SimpleGraph.mem_edgeFinset.mp h)
    simp [abfaParams, abpdBetaFieldParams, paramOn,
      FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
      abbCoupling, hxy, he, pBeta]




theorem abb_surface_conn_prob_eq_site {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (o x : S) (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (o : Option (sctBox d n)) {(x : Option (sctBox d n))}) =
      probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ
          (abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc o))
          {abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc x)}) := by
  let H := withGhost (sctBoxGraph d n)
  let T := abbPhysicalSurface d n S
  let K := abbSiteSurface d n S
  let GS := H.induce (S : Set (Option (sctBox d n)))
  let GT := (sctBoxGraph d n).induce (T : Set (sctBox d n))
  let GK := (hypercubicLattice d).induce (K : Set (Site d))
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  let qS : Sym2 S → Real := fun e ↦ p (Sym2.map Subtype.val e)
  let qT : Sym2 T → Real := fun e ↦
    qS ((abbEdgeEquiv (abbSurfaceEquiv hocc)).symm e)
  let r : Real := pBeta 1 beta
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem (sctBoxGraph d n) (abbCoupling d n) hJ beta h hbeta hh
  have hqT : ∀ e, 0 ≤ qT e ∧ qT e ≤ 1 := by
    intro e
    exact hp _
  have hr0 : 0 ≤ r := pBeta_nonneg (by simpa using hbeta)
  have hr1 : r ≤ 1 := (pBeta_lt_one 1 beta).le
  have hqT_edge (a b : T) (hab : GT.Adj a b) : qT s(a, b) = r := by
    have habBox : (sctBoxGraph d n).Adj (a : sctBox d n)
        (b : sctBox d n) := hab
    have hinv : (abbEdgeEquiv (abbSurfaceEquiv hocc)).symm s(a, b) =
        s((abbSurfaceEquiv hocc).symm a,
          (abbSurfaceEquiv hocc).symm b) := by
      apply (abbEdgeEquiv (abbSurfaceEquiv hocc)).injective
      simp [abbEdgeEquiv_mk]
    simp only [qT, qS, p, r]
    rw [hinv, Sym2.map_mk, abbSurfaceEquiv_symm_apply,
      abbSurfaceEquiv_symm_apply]
    rw [abbParams_some_some d n beta h]
    simp [habBox]
  let D : Finset (Sym2 T) := Finset.univ.filter fun e ↦ qT e = r
  have hDedge : ∀ a b, GT.Adj a b → s(a, b) ∈ D := by
    intro a b hab
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hqT_edge a b hab
  calc
    probV p (connEvent H (S : Set _) (o : Option (sctBox d n))
        {(x : Option (sctBox d n))}) =
        probV qS (connEvent GS Set.univ o {x}) := by
      exact abb_probV_connEvent_eq_induce H p (fun e ↦ (hp e).1)
        (fun e ↦ (hp e).2) S o x
    _ = probV qT
        (connEvent GT Set.univ (abbSurfaceEquiv hocc o)
          {abbSurfaceEquiv hocc x}) := by
      exact abb_probV_connEvent_relabel GS GT (abbSurfaceEquiv hocc)
        (abbSurfaceEquiv_adj hocc) qS o x
    _ = probV (fun _ : Sym2 T ↦ r)
        (connEvent GT Set.univ (abbSurfaceEquiv hocc o)
          {abbSurfaceEquiv hocc x}) := by
      apply abb_probV_eq_of_agreeOn qT (fun _ : Sym2 T ↦ r)
        (fun e ↦ (hqT e).1) (fun e ↦ (hqT e).2)
        (fun _ ↦ hr0) (fun _ ↦ hr1) _ D
        (abb_connEvent_univ_dependsOn_edges GT D hDedge
          (abbSurfaceEquiv hocc o) (abbSurfaceEquiv hocc x))
      intro e he
      exact (Finset.mem_filter.mp he).2
    _ = probV (fun _ : Sym2 K ↦ r)
        (connEvent GK Set.univ
          (abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc o))
          {abbSiteSurfaceEquiv d n S (abbSurfaceEquiv hocc x)}) := by
      simpa only [GT, GK, T, K, r] using
        (abb_probV_connEvent_relabel GT GK (abbSiteSurfaceEquiv d n S)
          (abbSiteSurfaceEquiv_adj S) (fun _ : Sym2 T ↦ r)
          (abbSurfaceEquiv hocc o) (abbSurfaceEquiv hocc x))

set_option maxHeartbeats 800000 in



theorem abb_connWithinProb_eq_probV_induce {d : Nat}
    (p : NNReal) (hp : p ≤ 1) (T : Finset (Site d)) (x : Site d)
    (ho : origin d ∈ T) (hx : x ∈ T) :
    connWithinProb d p hp T x =
      probV (fun _ : Sym2 T ↦ (p : Real))
        (connEvent ((hypercubicLattice d).induce (T : Set _)) Set.univ
          (⟨origin d, ho⟩ : T) {(⟨x, hx⟩ : T)}) := by
  let A := connEvent (hypercubicLattice d) (T : Set (Site d))
    (origin d) {x}
  let F := abigInternalEdges T
  let AI := connEvent ((hypercubicLattice d).induce (T : Set (Site d)))
    Set.univ (⟨origin d, ho⟩ : T) {(⟨x, hx⟩ : T)}
  have hAeq : A = withinConnEvent d (T : Set (Site d)) (origin d) x :=
    shk_connEvent_singleton_eq_connWithinEvent (T : Set (Site d))
      (origin d) x
  have hdep : StatMech.DependsOn A (F : Set (Sym2 (Site d))) :=
    abig_connEvent_dependsOn (hypercubicLattice d) T (origin d) x
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F hdep
  have hmeasure :
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp =
        inhomBernoulliProductMeasure (fun _ : Sym2 (Site d) ↦ p)
          (fun _ ↦ hp) := rfl
  rw [connWithinProb_eq p hp T x (by simpa using ho) (by simpa using hx),
    ← hAeq, hmeasure, hAcyl]
  calc
    (inhomBernoulliProductMeasure (fun _ : Sym2 (Site d) ↦ p)
        (fun _ ↦ hp)).real
        (MeasureTheory.cylinder F (ih_section A F)) =
      (inhomBernoulliProductMeasure (fun _ : F ↦ p) (fun _ ↦ hp)).real
        (ih_section A F) :=
      inhom_realProb_cylinder (fun _ : Sym2 (Site d) ↦ p)
        (fun _ ↦ hp) F _
    _ = probV (fun _ : F ↦ (p : Real)) (ih_section A F) := by
      exact abb_hom_real_eq_probV p hp (ih_section A F)
    _ = probV (fun _ : Sym2 T ↦ (p : Real)) AI := by
      exact abb_probV_section_const_eq_induce (p : Real)
        (hypercubicLattice d) T ⟨origin d, ho⟩ ⟨x, hx⟩



theorem abb_bondParam_coe_eq_pBeta (beta : Real) (hbeta : 0 ≤ beta) :
    (bondParam beta : Real) = pBeta 1 beta := by
  rw [bondParam, Real.coe_toNNReal]
  · simp [pBeta]
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))



theorem abb_surface_conn_prob_eq_connWithin {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (x : sctBox d n) (hx : some x ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (some (sctBoxOrigin d n)) {some x}) =
      connWithinProb d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) (x : Site d) := by
  let os : S := ⟨some (sctBoxOrigin d n), ho⟩
  let xs : S := ⟨some x, hx⟩
  let op : abbPhysicalSurface d n S := abbSurfaceEquiv hocc os
  let xp : abbPhysicalSurface d n S := abbSurfaceEquiv hocc xs
  let oz : abbSiteSurface d n S := abbSiteSurfaceEquiv d n S op
  let xz : abbSiteSurface d n S := abbSiteSurfaceEquiv d n S xp
  have hoSite : origin d ∈ abbSiteSurface d n S := by
    apply mem_abbSiteSurface_iff.mpr
    refine ⟨(sctBoxOrigin d n).property, ?_⟩
    simpa [StatMech.Percolation.origin, sctBoxOrigin] using ho
  have hxSite : (x : Site d) ∈ abbSiteSurface d n S := by
    apply mem_abbSiteSurface_iff.mpr
    exact ⟨x.property, hx⟩
  have hoz : oz = (⟨origin d, hoSite⟩ : abbSiteSurface d n S) := by
    apply Subtype.ext
    simp [oz, op, os, abbSurfaceEquiv_mk_some,
      StatMech.Percolation.origin, sctBoxOrigin]
    rfl
  have hxz : xz = (⟨(x : Site d), hxSite⟩ : abbSiteSurface d n S) := by
    apply Subtype.ext
    simp [xz, xp, xs, abbSurfaceEquiv_mk_some]
  have hfinite := abb_surface_conn_prob_eq_site hocc os xs beta h hbeta hh
  have hlattice := abb_connWithinProb_eq_probV_induce
    (bondParam beta) (bondParam_le_one beta) (abbSiteSurface d n S)
    (x : Site d) hoSite hxSite
  rw [abb_bondParam_coe_eq_pBeta beta hbeta] at hlattice
  calc
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
          (some (sctBoxOrigin d n)) {some x}) =
      probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ oz {xz}) := hfinite
    _ = probV (fun _ : Sym2 (abbSiteSurface d n S) ↦ pBeta 1 beta)
        (connEvent ((hypercubicLattice d).induce
          (abbSiteSurface d n S : Set _)) Set.univ
          ⟨origin d, hoSite⟩ {⟨(x : Site d), hxSite⟩}) := by
      rw [hoz, hxz]
    _ = connWithinProb d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) (x : Site d) := hlattice.symm


theorem abb_surface_avoids_boundary {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) {x : sctBox d n} (hx : some x ∈ S) :
    (x : Site d) ∉ vertexBoundary d n := by
  have hdisj := mpi_surfaceEvent_nonempty_disjoint
    (withGhost (sctBoxGraph d n)) (abbTarget d n) S hocc
  intro hxb
  exact Set.disjoint_left.mp hdisj (by simpa using hx)
    ((some_mem_abbTarget_iff d n x).mpr hxb)



theorem abbSiteSurface_subset_innerBox {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    (abbSiteSurface d n S : Set (Site d)) ⊆ box d (n - 1) := by
  intro x hx
  obtain ⟨hxbox, hxS⟩ := mem_abbSiteSurface_iff.mp hx
  exact Classical.byContradiction fun hxinner =>
    abb_surface_avoids_boundary hocc hxS ⟨hxbox, hxinner⟩



theorem origin_mem_abbSiteSurface {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (ho : some (sctBoxOrigin d n) ∈ S) :
    origin d ∈ abbSiteSurface d n S := by
  apply mem_abbSiteSurface_iff.mpr
  refine ⟨(sctBoxOrigin d n).2, ?_⟩
  simpa [origin, sctBoxOrigin] using ho



theorem abb_phi_ge_one_projected {d n : Nat} {p : NNReal}
    (hp : p ≤ 1) (hgt : tildePc d < p)
    {S : Finset (Option (sctBox d n))}
    (ho : some (sctBoxOrigin d n) ∈ S) :
    1 ≤ phi d p hp (abbSiteSurface d n S) := by
  exact phi_ge_one_of_gt_tildePc hp hgt (abbSiteSurface d n S)
    (origin_mem_abbSiteSurface ho)



def abbPairToSite (d n : Nat)
    (q : Option (sctBox d n) × Option (sctBox d n)) : Site d × Site d :=
  (q.1.elim (origin d) Subtype.val,
    q.2.elim (origin d) Subtype.val)

@[simp] theorem abbPairToSite_some_some (d n : Nat) (x y : sctBox d n) :
    abbPairToSite d n (some x, some y) = ((x : Site d), (y : Site d)) := rfl


noncomputable def abbPhysicalBoundaryPairs (d n : Nat)
    (S : Finset (Option (sctBox d n))) :
    Finset (Option (sctBox d n) × Option (sctBox d n)) :=
  (shk_boundaryPairs (withGhost (sctBoxGraph d n)) S).filter fun q ↦
    s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n)

@[simp] theorem mem_abbPhysicalBoundaryPairs_iff {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    {q : Option (sctBox d n) × Option (sctBox d n)} :
    q ∈ abbPhysicalBoundaryPairs d n S ↔
      q ∈ shk_boundaryPairs (withGhost (sctBoxGraph d n)) S ∧
        s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n) := by
  simp [abbPhysicalBoundaryPairs]


theorem abb_origEdge_endpoints_some {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : Option V} (h : s(a, b) ∈ FieldGhostDict.origEdges G) :
    ∃ x y : V, a = some x ∧ b = some y := by
  rw [FieldGhostDict.origEdges, Finset.mem_image] at h
  obtain ⟨e, he, hmap⟩ := h
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hmap
      rcases hmap with hmap | hmap
      · exact ⟨x, y, hmap.1.symm, hmap.2.symm⟩
      · exact ⟨y, x, hmap.2.symm, hmap.1.symm⟩



theorem abbPairToSite_mem_boundaryEdges {d n : Nat}
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    {q : Option (sctBox d n) × Option (sctBox d n)}
    (hq : q ∈ abbPhysicalBoundaryPairs d n S) :
    abbPairToSite d n q ∈ boundaryEdges d (abbSiteSurface d n S) := by
  obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq
  obtain ⟨hq1S, hq2S, hqadj⟩ :=
    (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mp hqbd
  obtain ⟨a, b, hqa, hqb⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
  have hqeq : q = (some a, some b) := Prod.ext hqa hqb
  subst q
  rw [abbPairToSite_some_some]
  apply shk_mem_boundaryEdges_iff.mpr
  refine ⟨?_, ?_, ?_⟩
  · exact mem_abbSiteSurface_iff.mpr ⟨a.property, hq1S⟩
  · intro hb
    obtain ⟨hbbox, hbS⟩ := mem_abbSiteSurface_iff.mp hb
    have hbeq : (⟨(b : Site d), hbbox⟩ : sctBox d n) = b :=
      Subtype.ext rfl
    exact hq2S (by simpa [hbeq] using hbS)
  · simpa [withGhost, sctBoxGraph] using hqadj


theorem abbPairToSite_injectiveOn {d n : Nat}
    {S : Finset (Option (sctBox d n))} :
    Set.InjOn (abbPairToSite d n)
      (abbPhysicalBoundaryPairs d n S : Set _) := by
  intro q hq r hr hqr
  obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq
  obtain ⟨hrbd, hrorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hr
  obtain ⟨a, b, hqa, hqb⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
  obtain ⟨c, e, hrc, hre⟩ :=
    abb_origEdge_endpoints_some (sctBoxGraph d n) hrorig
  have hqeq : q = (some a, some b) := Prod.ext hqa hqb
  have hreq : r = (some c, some e) := Prod.ext hrc hre
  subst q
  subst r
  simp only [abbPairToSite_some_some] at hqr
  have hac : a = c := Subtype.ext (congrArg Prod.fst hqr)
  have hbe : b = e := Subtype.ext (congrArg Prod.snd hqr)
  subst c
  subst e
  rfl



theorem exists_abbPhysicalBoundaryPair {d n : Nat}
    (hn : 0 < n) {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    {e : Site d × Site d}
    (he : e ∈ boundaryEdges d (abbSiteSurface d n S)) :
    ∃ q ∈ abbPhysicalBoundaryPairs d n S, abbPairToSite d n q = e := by
  obtain ⟨huS, hvS, hadj⟩ := shk_mem_boundaryEdges_iff.mp he
  obtain ⟨hubox, huGhost⟩ := mem_abbSiteSurface_iff.mp huS
  have huinner : e.1 ∈ box d (n - 1) :=
    abbSiteSurface_subset_innerBox hocc huS
  have hvbox : e.2 ∈ box d n := by
    have hstep := adj_box_step huinner hadj
    rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')] at hstep
  let u : sctBox d n := ⟨e.1, hubox⟩
  let v : sctBox d n := ⟨e.2, hvbox⟩
  let q : Option (sctBox d n) × Option (sctBox d n) := (some u, some v)
  refine ⟨q, ?_, ?_⟩
  · apply mem_abbPhysicalBoundaryPairs_iff.mpr
    constructor
    · apply (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mpr
      refine ⟨?_, ?_, ?_⟩
      · exact huGhost
      · intro hvGhost
        apply hvS
        exact mem_abbSiteSurface_iff.mpr ⟨hvbox, hvGhost⟩
      · change (sctBoxGraph d n).Adj u v
        exact hadj
    · rw [FieldGhostDict.origEdges, Finset.mem_image]
      refine ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr ?_, ?_⟩
      · exact hadj
      · simp [q]
  · rcases e with ⟨a, b⟩
    rfl



theorem image_abbPhysicalBoundaryPairs {d n : Nat}
    (hn : 0 < n) {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty) :
    (abbPhysicalBoundaryPairs d n S).image (abbPairToSite d n) =
      boundaryEdges d (abbSiteSurface d n S) := by
  ext e
  constructor
  · intro he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    exact abbPairToSite_mem_boundaryEdges hocc hq
  · intro he
    obtain ⟨q, hq, hqe⟩ := exists_abbPhysicalBoundaryPair hn hocc he
    exact Finset.mem_image.mpr ⟨q, hq, hqe⟩



theorem abbPhi_eq_phi {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abbPhi d n beta h S =
      phi d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) := by
  let P := abbPhysicalBoundaryPairs d n S
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  have hterm : ∀ q ∈ P,
      p s(q.1, q.2) *
          probV p (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
            (some (sctBoxOrigin d n)) {q.1}) =
        (bondParam beta : Real) *
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) (abbPairToSite d n q).1 := by
    intro q hq
    have hq' : q ∈ abbPhysicalBoundaryPairs d n S := hq
    obtain ⟨hqbd, hqorig⟩ := mem_abbPhysicalBoundaryPairs_iff.mp hq'
    obtain ⟨hq1S, hq2S, hqadj⟩ :=
      (shk_mem_boundaryPairs (withGhost (sctBoxGraph d n)) S).mp hqbd
    obtain ⟨a, b, hqa, hqb⟩ :=
      abb_origEdge_endpoints_some (sctBoxGraph d n) hqorig
    have hqeq : q = (some a, some b) := Prod.ext hqa hqb
    subst q
    have hab : (sctBoxGraph d n).Adj a b := by
      simpa [withGhost] using hqadj
    simp only [Prod.fst, Prod.snd, abbPairToSite_some_some]
    dsimp only [p]
    rw [abbParams_some_some d n beta h, if_pos hab,
      abb_bondParam_coe_eq_pBeta beta hbeta]
    rw [abb_surface_conn_prob_eq_connWithin hocc ho a hq1S
      beta h hbeta hh]
  calc
    abbPhi d n beta h S =
        ∑ q ∈ P,
          p s(q.1, q.2) *
            probV p (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
              (some (sctBoxOrigin d n)) {q.1}) := by
      unfold abbPhi abmgTargetPhi mtrPhi
      simp only [P, p, abbPhysicalBoundaryPairs, Finset.sum_filter]
    _ = ∑ q ∈ P, (bondParam beta : Real) *
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) (abbPairToSite d n q).1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q hq
    _ = (bondParam beta : Real) *
        ∑ e ∈ boundaryEdges d (abbSiteSurface d n S),
          connWithinProb d (bondParam beta) (bondParam_le_one beta)
            (abbSiteSurface d n S) e.1 := by
      rw [← image_abbPhysicalBoundaryPairs hn hocc]
      rw [Finset.mul_sum]
      rw [Finset.sum_image (abbPairToSite_injectiveOn
        (d := d) (n := n) (S := S))]
    _ = phi d (bondParam beta) (bondParam_le_one beta)
        (abbSiteSurface d n S) := by
      rfl



theorem abbPhi_ge_one_of_gt_tildePc {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hgt : tildePc d < bondParam beta) :
    1 ≤ abbPhi d n beta h S := by
  rw [abbPhi_eq_phi hn hocc ho beta h hbeta hh]
  exact phi_ge_one_of_gt_tildePc (bondParam_le_one beta) hgt
    (abbSiteSurface d n S) (origin_mem_abbSiteSurface ho)



theorem abbPhi_differentiableAt_beta (d n : Nat)
    (S : Finset (Option (sctBox d n))) (beta h : Real) :
    DifferentiableAt Real (fun b ↦ abbPhi d n b h S) beta := by
  have hparam : ∀ e : Sym2 (Option (sctBox d n)),
      DifferentiableAt Real
        (fun b ↦ abfaParams (sctBoxGraph d n) (abbCoupling d n) b h e)
        beta := by
    intro e
    unfold abfaParams abpdBetaFieldParams paramOn
    by_cases he : e ∈ FieldGhostDict.ghostEdges (sctBox d n)
    · simp [he]
    · simp [he, pBeta]
  have hprob : ∀ q : Option (sctBox d n) × Option (sctBox d n),
      DifferentiableAt Real (fun b ↦
        probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) b h)
          (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
            (some (sctBoxOrigin d n)) {q.1})) beta := by
    intro q
    have hjoint := abfa_differentiableAt_prob_joint
      (sctBoxGraph d n) (abbCoupling d n)
      (connEvent (withGhost (sctBoxGraph d n)) (S : Set _)
        (some (sctBoxOrigin d n)) {q.1}) beta h
    have hline : DifferentiableAt Real (fun b : Real ↦ (b, h)) beta :=
      differentiableAt_id.prodMk (differentiableAt_const h)
    simpa [Function.comp_def, Function.uncurry] using
      hjoint.comp beta hline
  unfold abbPhi abmgTargetPhi mtrPhi
  apply DifferentiableAt.fun_sum
  intro q hq
  by_cases he : s(q.1, q.2) ∈ FieldGhostDict.origEdges (sctBoxGraph d n)
  · simp only [he, if_true]
    exact (hparam s(q.1, q.2)).mul (hprob q)
  · simp [he]



theorem abbPhi_ge_one_of_tildePc_le {d n : Nat} (hn : 0 < n)
    {S : Finset (Option (sctBox d n))}
    (hocc : (mpiSurfaceEvent (withGhost (sctBoxGraph d n))
      (abbTarget d n) S).Nonempty)
    (ho : some (sctBoxOrigin d n) ∈ S)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hge : tildePc d ≤ bondParam beta) :
    1 ≤ abbPhi d n beta h S := by
  let b : Nat → Real := fun k ↦ beta + 1 / ((k : Real) + 1)
  have hb_tendsto : Tendsto b atTop (nhds beta) := by
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
    simpa only [b, add_zero] using tendsto_const_nhds.add hz
  have hphi_tendsto : Tendsto (fun k ↦ abbPhi d n (b k) h S)
      atTop (nhds (abbPhi d n beta h S)) :=
    (abbPhi_differentiableAt_beta d n S beta h).continuousAt.tendsto.comp
      hb_tendsto
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hphi_tendsto
  apply Filter.Eventually.of_forall
  intro k
  have hbk : beta < b k := by
    dsimp [b]
    have hk : 0 < 1 / ((k : Real) + 1) := by positivity
    linarith
  have hbk0 : 0 ≤ b k := hbeta.trans hbk.le
  have hpgtReal : (bondParam beta : Real) < (bondParam (b k) : Real) := by
    rw [abb_bondParam_coe_eq_pBeta beta hbeta,
      abb_bondParam_coe_eq_pBeta (b k) hbk0]
    exact pBeta_strictMono (J := (1 : Real)) one_pos hbk
  have hpgt : bondParam beta < bondParam (b k) := by
    exact NNReal.coe_lt_coe.mp hpgtReal
  exact abbPhi_ge_one_of_gt_tildePc hn hocc ho (b k) h hbk0 hh
    (hge.trans_lt hpgt)




theorem abbMag_meanfield_of_gt_tildePc {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hgt : tildePc d < bondParam beta) :
    1 - abbMag d n beta h ≤
      beta * deriv (fun b ↦ abbMag d n b h) beta := by
  apply abbMag_meanfield d n beta h hbeta hh
  intro S ho hocc
  exact abbPhi_ge_one_of_gt_tildePc hn hocc ho beta h hbeta hh hgt


theorem abbMag_meanfield_of_tildePc_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h)
    (hge : tildePc d ≤ bondParam beta) :
    1 - abbMag d n beta h ≤
      beta * deriv (fun b ↦ abbMag d n b h) beta := by
  apply abbMag_meanfield d n beta h hbeta hh
  intro S ho hocc
  exact abbPhi_ge_one_of_tildePc_le hn hocc ho beta h hbeta hh hge

end Sharpness
end StatMech

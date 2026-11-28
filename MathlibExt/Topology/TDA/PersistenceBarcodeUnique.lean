/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.TDA.PersistenceModule
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Uniqueness of the barcode of an interval-decomposable persistence module

If a persistence module over `ℝ` is a direct sum of interval modules of nonempty order-connected
sets in two ways, the two families of intervals agree up to a bijection of the index types
(`intervalModule_decomposition_unique`; Chazal, de Silva, Glisse and Oudot, *The structure and
stability of persistence modules*, arXiv:1207.3674, Thm. 1.3, which deduces it from Azumaya's
theorem).

The proof here avoids Azumaya's theorem and compares multiplicities directly. Fix a nonempty
interval `L`, a point `t ∈ L`, and an isomorphism `e : ⊕ᵢ k_{I i} ≅ ⊕ⱼ k_{J j}`. Let `p` be the
endomorphism of `⊕ⱼ k_{J j}` that keeps the summands with `J j = L` and kills the others. For
the indices `i` with `I i = L`, the vectors `p (e (1ᵢ))` of the fibre at `t` (where `1ᵢ` is the
unit vector of the summand `i`) are linearly independent: the functionals `y ↦ (e⁻¹ y)ᵢ'` form
a dual family, because a composite `k_L ⟶ k_{J j} ⟶ k_L` that is nonzero at `t` forces
`J j = L`, and the fibre at `t` of a coproduct is spanned by its summands. These vectors lie in
the span of the unit vectors of the summands with `J j = L`, so
`#{i | I i = L} ≤ #{j | J j = L}`. The reverse inequality comes from `e.symm`, and the bijection
is assembled interval by interval.
-/

@[expose] public section

open CategoryTheory Limits MathlibExt.Topology.TDA

universe u

namespace MathlibExt.Topology.PersistenceModuleWanted

namespace IntervalModuleDecompositionUnique

section Coproduct

variable {k : Type u} [Field k] {D : Type*} [Category D] {κ : Type u}

/-- The fibre of a coproduct of persistence modules is spanned by the images of the summands. -/
private theorem iSup_range_eq_top (G : κ → D ⥤ ModuleCat.{u} k) (t : D) :
    ⨆ j, LinearMap.range ((Sigma.ι G j).app t).hom = ⊤ := by
  set N := ⨆ j, LinearMap.range ((Sigma.ι G j).app t).hom
  let q : (∐ G).obj t ⟶ ModuleCat.of k ((∐ G).obj t ⧸ N) := ModuleCat.ofHom N.mkQ
  have hq : (sigmaObjIso G t).inv ≫ q = 0 := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [ι_comp_sigmaObjIso_inv_assoc, comp_zero]
    ext x
    simpa [q] using Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ x)
  have hq' : q = 0 := by
    rw [← Category.id_comp q, ← (sigmaObjIso G t).hom_inv_id, Category.assoc, hq, comp_zero]
  rw [eq_top_iff]
  intro x _
  have := congrArg (fun φ => φ.hom x) hq'
  simpa [q] using this

/-- Every vector of the fibre of a coproduct of persistence modules is the finite sum of its
components along the summands. -/
private theorem exists_finset_sum [DecidableEq κ] (G : κ → D ⥤ ModuleCat.{u} k) (t : D)
    (y : (∐ G).obj t) :
    ∃ F : Finset κ, ∑ j ∈ F, ((Sigma.ι G j).app t).hom (((Sigma.π G j).app t).hom y) = y := by
  have hy : y ∈ ⨆ j, LinearMap.range ((Sigma.ι G j).app t).hom := by
    rw [iSup_range_eq_top]; trivial
  suffices h : ∃ F : Finset κ, ∀ F' : Finset κ, F ⊆ F' →
      ∑ j ∈ F', ((Sigma.ι G j).app t).hom (((Sigma.π G j).app t).hom y) = y by
    obtain ⟨F, hF⟩ := h
    exact ⟨F, hF F subset_rfl⟩
  refine Submodule.iSup_induction (motive := fun y => ∃ F : Finset κ, ∀ F' : Finset κ, F ⊆ F' →
      ∑ j ∈ F', ((Sigma.ι G j).app t).hom (((Sigma.π G j).app t).hom y) = y) _ hy ?_ ?_ ?_
  · rintro j _ ⟨z, rfl⟩
    refine ⟨{j}, fun F' hF' => ?_⟩
    rw [Finset.sum_eq_single j]
    · have := congrArg (fun φ => (φ.app t).hom z) (Sigma.ι_π_eq_id G j)
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.id_app,
        ModuleCat.hom_id, LinearMap.id_apply] at this
      rw [this]
    · intro j' _ hj'
      have := congrArg (fun φ => (φ.app t).hom z) (Sigma.ι_π_of_ne G (Ne.symm hj'))
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.app_zero,
        ModuleCat.hom_zero, LinearMap.zero_apply] at this
      rw [this, map_zero]
    · intro hj
      exact absurd (hF' (Finset.mem_singleton_self j)) hj
  · exact ⟨∅, fun F' _ => by simp⟩
  · rintro x y ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨F₁ ∪ F₂, fun F' hF' => ?_⟩
    simp only [map_add, Finset.sum_add_distrib]
    rw [h₁ F' (Finset.union_subset_left hF'), h₂ F' (Finset.union_subset_right hF')]

end Coproduct

section IntervalModule

variable {k : Type u} [Field k]

/-- An element of the fibre of an interval module outside its interval vanishes. -/
private theorem eq_zero_of_notMem {X : Set ℝ} (hX : X.OrdConnected) {s : ℝ} (hs : s ∉ X)
    (x : (intervalModule k X hX).obj s) : x = 0 :=
  funext fun p => absurd p.down hs

/-- An element of the fibre of an interval module inside its interval is determined by its
value. -/
private theorem eq_of_apply_eq {X : Set ℝ} (hX : X.OrdConnected) {s : ℝ} (hs : s ∈ X)
    {x y : (intervalModule k X hX).obj s} (h : x ⟨hs⟩ = y ⟨hs⟩) : x = y :=
  funext fun _ => h

open scoped Classical in
/-- The structure maps of an interval module, evaluated at a point. -/
private theorem map_apply {X : Set ℝ} (hX : X.OrdConnected) {s t : ℝ} (hst : s ≤ t)
    (x : (intervalModule k X hX).obj s) (p : PLift (t ∈ X)) :
    ((intervalModule k X hX).map (homOfLE hst)).hom x p = if hs : s ∈ X then x ⟨hs⟩ else 0 :=
  rfl

open scoped Classical in
/-- Naturality of a morphism of interval modules, evaluated at a point. -/
private theorem app_map_apply {A B : Set ℝ} {hA : A.OrdConnected} {hB : B.OrdConnected}
    (φ : intervalModule k A hA ⟶ intervalModule k B hB) {s t : ℝ} (hst : s ≤ t)
    (x : (intervalModule k A hA).obj s) (p : PLift (t ∈ B)) :
    (φ.app t).hom (((intervalModule k A hA).map (homOfLE hst)).hom x) p =
      if hs : s ∈ B then (φ.app s).hom x ⟨hs⟩ else 0 :=
  congrFun (congrArg (fun ψ => ψ.hom x) (φ.naturality (homOfLE hst))) p

/-- If a composite `k_A ⟶ k_B ⟶ k_A` of morphisms of interval modules is nonzero at a point of
`A`, then `B = A`: points of `B` outside `A` would force the first or the second map to vanish at
that point, and points of `A` outside `B` would force the composite, which is constant on `A`,
to vanish. -/
private theorem eq_of_comp_app_ne_zero {A B C : Set ℝ} {hA : A.OrdConnected}
    {hB : B.OrdConnected} {hC : C.OrdConnected} (f : intervalModule k A hA ⟶ intervalModule k B hB)
    (g : intervalModule k B hB ⟶ intervalModule k C hC) (hAC : A = C) {t : ℝ} (htA : t ∈ A)
    (htC : t ∈ C) (h : (g.app t).hom ((f.app t).hom fun _ => (1 : k)) ⟨htC⟩ ≠ 0) : B = A := by
  subst hAC
  set one : (intervalModule k A hA).obj t := fun _ => (1 : k)
  set y : (intervalModule k B hB).obj t := (f.app t).hom one with hy
  have htB : t ∈ B := by
    by_contra htB
    apply h
    rw [eq_zero_of_notMem hB htB y, map_zero]
    rfl
  apply Set.Subset.antisymm
  · intro s hsB
    by_contra hsA
    rcases le_total s t with hst | hts
    · -- `g` vanishes at `t`, since `y` comes from `s`, where `k_A` vanishes
      apply h
      let z : (intervalModule k B hB).obj s := fun _ => y ⟨htB⟩
      have hz : ((intervalModule k B hB).map (homOfLE hst)).hom z = y :=
        eq_of_apply_eq hB htB (by rw [map_apply, dite_eq_left hsB])
      rw [← hz, app_map_apply g hst z, dite_eq_right hsA]
    · -- `f` vanishes at `t`, since `k_A` vanishes at `s ≥ t` while `k_B` does not
      apply h
      have h1 := app_map_apply f hts one ⟨hsB⟩
      rw [eq_zero_of_notMem hA hsA (((intervalModule k A hA).map (homOfLE hts)).hom one),
        map_zero, dite_eq_left htB] at h1
      have h2 : y = 0 := eq_of_apply_eq hB htB h1.symm
      rw [h2, map_zero]
      rfl
  · intro s hsA
    by_contra hsB
    rcases le_total s t with hst | hts
    · apply h
      let one' : (intervalModule k A hA).obj s := fun _ => (1 : k)
      have h1 : ((intervalModule k A hA).map (homOfLE hst)).hom one' = one :=
        eq_of_apply_eq hA htA (by rw [map_apply, dite_eq_left hsA])
      have h2 : y = ((intervalModule k B hB).map (homOfLE hst)).hom ((f.app s).hom one') := by
        rw [hy, ← h1]
        exact funext fun p => app_map_apply f hst one' p
      rw [h2, eq_zero_of_notMem hB hsB ((f.app s).hom one'), map_zero, map_zero]
      rfl
    · apply h
      have h1 : (f.app s).hom (((intervalModule k A hA).map (homOfLE hts)).hom one) =
          ((intervalModule k B hB).map (homOfLE hts)).hom y :=
        funext fun p => app_map_apply f hts one p
      have h2 := app_map_apply g hts y ⟨hsA⟩
      rw [← h1, eq_zero_of_notMem hB hsB ((f.app s).hom _), map_zero, dite_eq_left htA] at h2
      exact h2.symm

/-- Evaluation of the fibre of an interval module at a point of the interval. -/
private def evalAt {X : Set ℝ} (hX : X.OrdConnected) {t : ℝ} (ht : t ∈ X) :
    (intervalModule k X hX).obj t →ₗ[k] k :=
  LinearMap.proj (R := k) (φ := fun _ : PLift (t ∈ X) => k) ⟨ht⟩

variable (k) in
/-- **The multiplicity of a bar can only grow along an isomorphism.** For an isomorphism of
direct sums of interval modules and a set `L`, there are at most as many summands with interval
`L` on the left as on the right. -/
private theorem card_le {ι κ : Type u} (I : ι → Set ℝ) (J : κ → Set ℝ)
    (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected)
    (hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected)
    (e : (∐ fun i => intervalModule k (I i) (hI i).2) ≅
      ∐ fun j => intervalModule k (J j) (hJ j).2)
    (L : Set ℝ) : Cardinal.mk {i // I i = L} ≤ Cardinal.mk {j // J j = L} := by
  classical
  rcases isEmpty_or_nonempty {i // I i = L} with hS | ⟨⟨i₀, hi₀⟩⟩
  · rw [Cardinal.mk_eq_zero]
    exact zero_le
  obtain ⟨t, ht⟩ : L.Nonempty := hi₀ ▸ (hI i₀).1
  set F := fun i => intervalModule k (I i) (hI i).2
  set G := fun j => intervalModule k (J j) (hJ j).2
  -- the projection onto the summands of `G` whose interval is `L`
  let p : (∐ G) ⟶ (∐ G) := Sigma.desc fun j => if J j = L then Sigma.ι G j else 0
  have hp_pos (j : κ) (hj : J j = L) (z : (G j).obj t) :
      (p.app t).hom (((Sigma.ι G j).app t).hom z) = ((Sigma.ι G j).app t).hom z := by
    have := congrArg (fun φ => (φ.app t).hom z)
      ((Sigma.ι_comp_desc (fun j => if J j = L then Sigma.ι G j else 0) j).trans (ite_eq_left hj))
    simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hp_neg (j : κ) (hj : ¬ J j = L) (z : (G j).obj t) :
      (p.app t).hom (((Sigma.ι G j).app t).hom z) = 0 := by
    have := congrArg (fun φ => (φ.app t).hom z)
      ((Sigma.ι_comp_desc (fun j => if J j = L then Sigma.ι G j else 0) j).trans
        (ite_eq_right hj))
    simpa only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, NatTrans.app_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply] using this
  have htI (i : {i // I i = L}) : t ∈ I i.1 := by rw [i.2]; exact ht
  let u (i : {i // I i = L}) : (∐ F).obj t := ((Sigma.ι F i.1).app t).hom fun _ => (1 : k)
  let v (i : {i // I i = L}) : (∐ G).obj t := (p.app t).hom ((e.hom.app t).hom (u i))
  -- the coordinate functionals
  let coord (i : {i // I i = L}) : (∐ G).obj t →ₗ[k] k :=
    (evalAt (hI i.1).2 (htI i)).comp (((Sigma.π F i.1).app t).hom.comp (e.inv.app t).hom)
  have key (i i' : {i // I i = L}) : coord i' (v i) = if i = i' then 1 else 0 := by
    obtain ⟨Fs, hFs⟩ := exists_finset_sum G t ((e.hom.app t).hom (u i))
    have h1 : coord i' (v i) = coord i' ((e.hom.app t).hom (u i)) := by
      change coord i' ((p.app t).hom ((e.hom.app t).hom (u i))) = _
      rw [← hFs]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : J j = L
      · rw [hp_pos j hj]
      · rw [hp_neg j hj, map_zero]
        symm
        by_contra hne
        apply hj
        rw [← i.2]
        exact eq_of_comp_app_ne_zero (Sigma.ι F i.1 ≫ e.hom ≫ Sigma.π G j)
          (Sigma.ι G j ≫ e.inv ≫ Sigma.π F i'.1) (i.2.trans i'.2.symm) (htI i) (htI i') hne
    rw [h1]
    have h2 := congrArg (fun φ => φ.hom (u i)) (Iso.hom_inv_id_app e t)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at h2
    change ((Sigma.π F i'.1).app t).hom ((e.inv.app t).hom ((e.hom.app t).hom (u i))) ⟨htI i'⟩ = _
    rw [h2]
    by_cases hii : i = i'
    · subst hii
      have h3 := congrArg (fun φ => (φ.app t).hom (fun _ => (1 : k))) (Sigma.ι_π_eq_id F i.1)
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, NatTrans.id_app, ModuleCat.hom_id] at h3
      rw [ite_eq_left rfl]
      exact congrFun h3 ⟨htI i⟩
    · have h3 := congrArg (fun φ => (φ.app t).hom (fun _ => (1 : k)))
        (Sigma.ι_π_of_ne F fun h => hii (Subtype.ext h))
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, NatTrans.app_zero,
        ModuleCat.hom_zero] at h3
      rw [ite_eq_right hii]
      exact congrFun h3 ⟨htI i'⟩
  have hli : LinearIndependent k v := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h1 := congrArg (coord i) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, key, smul_eq_mul, mul_ite, mul_one, mul_zero] at h1
    rwa [Finset.sum_ite_eq' s i g, ite_eq_left hi] at h1
  let w (j : {j // J j = L}) : (∐ G).obj t := ((Sigma.ι G j.1).app t).hom fun _ => (1 : k)
  have hspan (i : {i // I i = L}) : v i ∈ Submodule.span k (Set.range w) := by
    have hy : (e.hom.app t).hom (u i) ∈ ⨆ j, LinearMap.range ((Sigma.ι G j).app t).hom := by
      rw [iSup_range_eq_top]
      trivial
    refine Submodule.iSup_induction
      (motive := fun y => (p.app t).hom y ∈ Submodule.span k (Set.range w)) _ hy ?_ ?_ ?_
    · rintro j _ ⟨z, rfl⟩
      by_cases hj : J j = L
      · rw [hp_pos j hj z]
        have htJ : t ∈ J j := by rw [hj]; exact ht
        have hz : ((Sigma.ι G j).app t).hom z =
            evalAt (hJ j).2 htJ z • ((Sigma.ι G j).app t).hom fun _ => (1 : k) := by
          have hzz : z = evalAt (hJ j).2 htJ z • (fun _ => (1 : k) : (G j).obj t) :=
            eq_of_apply_eq (hJ j).2 htJ (mul_one _).symm
          exact (congrArg ((Sigma.ι G j).app t).hom hzz).trans (map_smul _ _ _)
        rw [hz]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
      · rw [hp_neg j hj z]
        exact Submodule.zero_mem _
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  set W := Submodule.span k (Set.range w)
  let v' (i : {i // I i = L}) : W := ⟨v i, hspan i⟩
  have hli' : LinearIndependent k v' := LinearIndependent.of_comp W.subtype hli
  calc Cardinal.mk {i // I i = L} ≤ Module.rank k W := hli'.cardinal_le_rank
    _ ≤ Cardinal.mk (Set.range w) := rank_span_le _
    _ ≤ Cardinal.mk {j // J j = L} := Cardinal.mk_range_le

end IntervalModule

end IntervalModuleDecompositionUnique

variable (k : Type u) [Field k]

open IntervalModuleDecompositionUnique in
/-- **The barcode is unique (Krull–Remak–Schmidt–Azumaya).** If a persistence module over `ℝ`
is a direct sum of interval modules in two ways, `⊕_{i ∈ ι} k_{I i} ≅ ⊕_{j ∈ κ} k_{J j}`, then
there is a bijection `σ : ι ≃ κ` with `J (σ i) = I i` for all `i`: the multiset of intervals is
an isomorphism invariant (Chazal, de Silva, Glisse and Oudot, *The structure and stability of
persistence modules*, arXiv:1207.3674, Thm. 1.3, from Azumaya's theorem). -/
theorem intervalModule_decomposition_unique {ι κ : Type u} (I : ι → Set ℝ)
    (J : κ → Set ℝ) (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected)
    (hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected)
    (e : (∐ fun i => intervalModule k (I i) (hI i).2) ≅
      ∐ fun j => intervalModule k (J j) (hJ j).2) :
    ∃ σ : ι ≃ κ, ∀ i, J (σ i) = I i := by
  have h (L : Set ℝ) : Nonempty ({i // I i = L} ≃ {j // J j = L}) :=
    Cardinal.eq.1 (le_antisymm (card_le k I J hI hJ e L) (card_le k J I hJ hI e.symm L))
  let τ (L : Set ℝ) := (h L).some
  exact ⟨(Equiv.sigmaFiberEquiv I).symm.trans
    ((Equiv.sigmaCongrRight τ).trans (Equiv.sigmaFiberEquiv J)), fun i => (τ (I i) ⟨i, rfl⟩).2⟩

end MathlibExt.Topology.PersistenceModuleWanted

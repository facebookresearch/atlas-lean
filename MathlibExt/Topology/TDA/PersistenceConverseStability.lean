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
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Converse stability for interval-decomposable persistence modules

A barcode matching at scale `δ` induces an interleaving of the interval-decomposable
persistence modules at every scale strictly greater than `δ`.
-/

@[expose] public section

open CategoryTheory Limits MathlibExt.Topology.TDA Metric

universe u

namespace MathlibExt.Topology.PersistenceModuleWanted

namespace InterleavingOfIsMatching

variable (k : Type u) [Field k]

/-- The identity on the coefficient field when both fibres are supported, and zero otherwise.
Use the interval module's fibre map on the disjoint union of the two index sets. -/
private noncomputable def intervalHom (I J : Set ℝ) (s t : ℝ) :
    ModuleCat.of k (PLift (s ∈ I) → k) ⟶ ModuleCat.of k (PLift (t ∈ J) → k) :=
  ModuleCat.ofHom (intervalModuleMap k
    (T := ℝ ⊕ ℝ) {x | x.elim (· ∈ I) (· ∈ J)} (.inl s) (.inr t))

private theorem intervalHom_comp_congr {I J J' K : Set ℝ} {s t t' r : ℝ}
    (h : s ∈ I → r ∈ K → (t ∈ J ↔ t' ∈ J')) :
    intervalHom k I J s t ≫ intervalHom k J K t r =
      intervalHom k I J' s t' ≫ intervalHom k J' K t' r := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun hr => ?_)
  by_cases hs : s ∈ I
  · by_cases ht : t ∈ J
    · have ht' := (h hs hr.down).mp ht
      simp [intervalHom, intervalModuleMap, hs, ht, ht']
      rfl
    · have ht' := mt (h hs hr.down).mpr ht
      simp [intervalHom, intervalModuleMap, ht, ht']
      rfl
  · by_cases ht : t ∈ J <;> by_cases ht' : t' ∈ J' <;>
      simp [intervalHom, intervalModuleMap, hs, ht, ht'] <;> rfl

private theorem intervalHom_comp {I J K : Set ℝ} {s t r : ℝ}
    (h : s ∈ I → r ∈ K → t ∈ J) :
    intervalHom k I J s t ≫ intervalHom k J K t r = intervalHom k I K s r := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun hr => ?_)
  by_cases hs : s ∈ I
  · have ht := h hs hr.down
    simp [intervalHom, intervalModuleMap, hs, ht]
    rfl
  · by_cases ht : t ∈ J <;> simp [intervalHom, intervalModuleMap, hs, ht] <;> rfl

private theorem intervalHom_eq_zero {I J : Set ℝ} {s t : ℝ}
    (h : s ∈ I → t ∉ J) : intervalHom k I J s t = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun ht => ?_)
  have hs : s ∉ I := fun hs => h hs ht.down
  simp [intervalHom, intervalModuleMap, hs]
  rfl

private theorem exists_mem_near {I J : Set ℝ} {ε x : ℝ} (hε : 0 < ε)
    (h : hausdorffEDist I J < ENNReal.ofReal ε) (hx : x ∈ I) :
    ∃ y ∈ J, x - ε < y ∧ y < x + ε := by
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx h
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε, Real.dist_eq, abs_lt] at hxy
  exact ⟨y, hy, by linarith [hxy.2], by linarith [hxy.1]⟩

private theorem intervalHom_natural {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {ε : ℝ} (hε : 0 < ε) (h : hausdorffEDist I J < ENNReal.ofReal ε) {s t : ℝ} (hst : s ≤ t) :
    (intervalModule k I hI).map (homOfLE hst) ≫ intervalHom k I J t (t + ε) =
      intervalHom k I J s (s + ε) ≫ (intervalModule k J hJ).map
        (homOfLE (add_le_add_left hst ε)) := by
  change intervalHom k I I s t ≫ intervalHom k I J t (t + ε) =
    intervalHom k I J s (s + ε) ≫ intervalHom k J J (s + ε) (t + ε)
  apply intervalHom_comp_congr
  intro hs ht
  constructor
  · intro _
    obtain ⟨y, hy, _, hy'⟩ := exists_mem_near hε h hs
    exact hJ.out hy ht ⟨hy'.le, add_le_add_left hst ε⟩
  · intro _
    rw [hausdorffEDist_comm] at h
    obtain ⟨y, hy, hy', _⟩ := exists_mem_near hε h ht
    exact hI.out hs hy ⟨hst, by linarith⟩

private theorem intervalHom_triangle {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    {ε : ℝ} (hε : 0 < ε) (h : hausdorffEDist I J < ENNReal.ofReal ε) (t : ℝ) :
    intervalHom k I J t (t + ε) ≫ intervalHom k J I (t + ε) (t + ε + ε) =
      (intervalModule k I hI).map (homOfLE (by linarith : t ≤ t + ε + ε)) := by
  change _ = intervalHom k I I t (t + ε + ε)
  apply intervalHom_comp
  intro ht ht'
  obtain ⟨x, hx, _, hxt⟩ := exists_mem_near hε h ht
  obtain ⟨y, hy, hty, _⟩ := exists_mem_near hε h ht'
  exact hJ.out hx hy ⟨hxt.le, by linarith⟩

private theorem intervalModule_map_eq_zero {I : Set ℝ} (hI : I.OrdConnected)
    {δ ε : ℝ} (hδε : δ < ε) (hε : 0 < ε) (h : ∃ a, I ⊆ Set.Icc a (a + 2 * δ)) (t : ℝ) :
    (intervalModule k I hI).map (homOfLE (by linarith : t ≤ t + ε + ε)) = 0 := by
  obtain ⟨a, ha⟩ := h
  change intervalHom k I I t (t + ε + ε) = 0
  apply intervalHom_eq_zero
  intro ht ht'
  linarith [(ha ht).1, (ha ht').2]

section Coproduct

variable {ι κ : Type u} {F : ι → ℝ ⥤ ModuleCat.{u} k} {G : κ → ℝ ⥤ ModuleCat.{u} k}

private noncomputable def cofanOfIso {U : ℝ ⥤ ModuleCat.{u} k} (e : U ≅ ∐ F) : Cofan F :=
  Cofan.mk U fun i => Sigma.ι F i ≫ e.inv

private noncomputable def isColimitCofanOfIso {U : ℝ ⥤ ModuleCat.{u} k} (e : U ≅ ∐ F) :
    IsColimit (cofanOfIso k e) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct F) (Cofan.ext e.symm fun _ => rfl)

variable {k} (c : Cofan F) (d : Cofan G) (hc : IsColimit c) (hd : IsColimit d)
  {M : ι → κ → Prop} {ε : ℝ}

private noncomputable def pointwiseColimit (t : ℝ) :
    IsColimit (Cofan.mk (c.pt.obj t) fun i => (c.inj i).app t) :=
  isColimitCofanMkObjOfIsColimit ((evaluation ℝ (ModuleCat k)).obj t) F c.inj hc

/-- On each matched summand, use its shifted map to its partner. Send unmatched summands to zero. -/
private noncomputable def matchingMap
    (f : ∀ i j, M i j → ∀ t : ℝ, (F i).obj t ⟶ (G j).obj (t + ε)) (t : ℝ) :
    c.pt.obj t ⟶ d.pt.obj (t + ε) := by
  classical
  exact Cofan.IsColimit.desc (pointwiseColimit c hc t) fun i =>
    if h : ∃ j, M i j then f i h.choose h.choose_spec t ≫ (d.inj h.choose).app (t + ε) else 0

variable (f : ∀ i j, M i j → ∀ t : ℝ, (F i).obj t ⟶ (G j).obj (t + ε))

private theorem inj_matchingMap_of_match
    (hM : ∀ i j j', M i j → M i j' → j = j') {i : ι} {j : κ} (hij : M i j) (t : ℝ) :
    (c.inj i).app t ≫ matchingMap c d hc f t = f i j hij t ≫ (d.inj j).app (t + ε) := by
  classical
  have h : ∃ j, M i j := ⟨j, hij⟩
  have hj : h.choose = j := hM i _ _ h.choose_spec hij
  unfold matchingMap
  change (Cofan.mk (c.pt.obj t) fun i => (c.inj i).app t).inj i ≫ _ = _
  rw [Cofan.IsColimit.fac, dite_eq_left h]
  subst j
  rfl

private theorem inj_matchingMap_of_unmatched {i : ι} (hi : ∀ j, ¬ M i j) (t : ℝ) :
    (c.inj i).app t ≫ matchingMap c d hc f t = 0 := by
  classical
  unfold matchingMap
  change (Cofan.mk (c.pt.obj t) fun i => (c.inj i).app t).inj i ≫ _ = _
  rw [Cofan.IsColimit.fac, dite_eq_right (not_exists.mpr hi)]

private theorem matchingMap_natural (hM : ∀ i j j', M i j → M i j' → j = j')
    (hf : ∀ i j (hij : M i j) (s t : ℝ) (hst : s ≤ t),
      (F i).map (homOfLE hst) ≫ f i j hij t =
        f i j hij s ≫ (G j).map (homOfLE (add_le_add_left hst ε)))
    (s t : ℝ) (hst : s ≤ t) :
    c.pt.map (homOfLE hst) ≫ matchingMap c d hc f t =
      matchingMap c d hc f s ≫ d.pt.map (homOfLE (add_le_add_left hst ε)) := by
  apply (pointwiseColimit c hc s).hom_ext
  intro ⟨i⟩
  change (c.inj i).app s ≫ _ = (c.inj i).app s ≫ _
  rw [reassoc_of% ((c.inj i).naturality (homOfLE hst)).symm]
  by_cases hi : ∃ j, M i j
  · obtain ⟨j, hij⟩ := hi
    rw [inj_matchingMap_of_match c d hc f hM hij t,
      reassoc_of% (inj_matchingMap_of_match c d hc f hM hij s),
      ← (d.inj j).naturality (homOfLE (add_le_add_left hst ε)),
      ← Category.assoc, hf i j hij s t hst, Category.assoc]
  · simp only [inj_matchingMap_of_unmatched c d hc f (not_exists.mp hi), comp_zero,
      reassoc_of% (inj_matchingMap_of_unmatched c d hc f (not_exists.mp hi) s), zero_comp]

private theorem matchingMap_triangle
    (g : ∀ j i, M i j → ∀ t : ℝ, (G j).obj t ⟶ (F i).obj (t + ε))
    (hM : ∀ i j j', M i j → M i j' → j = j') (hM' : ∀ j i i', M i j → M i' j → i = i')
    (hε : 0 ≤ ε)
    (hfg : ∀ i j (hij : M i j) (t : ℝ),
      f i j hij t ≫ g j i hij (t + ε) =
        (F i).map (homOfLE (by linarith : t ≤ t + ε + ε)))
    (hzero : ∀ i, (∀ j, ¬ M i j) → ∀ t : ℝ,
      (F i).map (homOfLE (by linarith : t ≤ t + ε + ε)) = 0)
    (t : ℝ) :
    matchingMap c d hc f t ≫ matchingMap d c hd (M := fun j i => M i j) g (t + ε) =
      c.pt.map (homOfLE (by linarith : t ≤ t + ε + ε)) := by
  apply (pointwiseColimit c hc t).hom_ext
  intro ⟨i⟩
  change (c.inj i).app t ≫ _ = (c.inj i).app t ≫ _
  rw [← (c.inj i).naturality (homOfLE (by linarith : t ≤ t + ε + ε))]
  by_cases hi : ∃ j, M i j
  · obtain ⟨j, hij⟩ := hi
    rw [reassoc_of% (inj_matchingMap_of_match c d hc f hM hij t),
      inj_matchingMap_of_match d c hd (M := fun j i => M i j) g hM' hij (t + ε),
      ← Category.assoc, hfg i j hij t]
  · have hi' := not_exists.mp hi
    simp only [reassoc_of% (inj_matchingMap_of_unmatched c d hc f hi' t), zero_comp,
      hzero i hi' t]

end Coproduct

end InterleavingOfIsMatching

variable (k : Type u) [Field k]

open InterleavingOfIsMatching in
/-- **Converse stability for decomposable modules.** If `U ≅ ⊕ k_{I i}` and `V ≅ ⊕ k_{J j}` are
direct sums of interval modules and there is a `δ`-matching between the barcodes `I` and `J`,
then `U` and `V` are `δ'`-interleaved for every `δ' > δ`; that is, the interleaving distance is
at most the bottleneck distance (Chazal, de Silva, Glisse and Oudot, arXiv:1207.3674,
Thm. 4.9). -/
theorem interleaving_of_isMatching {U V : ℝ ⥤ ModuleCat.{u} k}
    {ι κ : Type u} {I : ι → Set ℝ} {J : κ → Set ℝ}
    (hI : ∀ i, (I i).Nonempty ∧ (I i).OrdConnected)
    (hJ : ∀ j, (J j).Nonempty ∧ (J j).OrdConnected)
    (eU : U ≅ ∐ fun i => intervalModule k (I i) (hI i).2)
    (eV : V ≅ ∐ fun j => intervalModule k (J j) (hJ j).2)
    {δ : ℝ} (hM : IsMatching I J δ) {δ' : ℝ} (hδ' : δ < δ') :
    Nonempty (Interleaving U V δ') := by
  obtain ⟨hδ, M, hfun, hinj, hdist, hshortI, hshortJ⟩ := hM
  have hε : 0 < δ' := hδ.trans_lt hδ'
  have hclose i j (hij : M i j) :
      hausdorffEDist (I i) (J j) < ENNReal.ofReal δ' :=
    (hdist i j hij).trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.2 hδ')
  have hclose' j i (hij : M i j) :
      hausdorffEDist (J j) (I i) < ENNReal.ofReal δ' := by
    rw [hausdorffEDist_comm]
    exact hclose i j hij
  let Uc := cofanOfIso k eU
  let Vc := cofanOfIso k eV
  let hUc := isColimitCofanOfIso k eU
  let hVc := isColimitCofanOfIso k eV
  let φ (i : ι) (j : κ) (_ : M i j) (t : ℝ) := intervalHom k (I i) (J j) t (t + δ')
  let ψ (j : κ) (i : ι) (_ : M i j) (t : ℝ) := intervalHom k (J j) (I i) t (t + δ')
  have hinj' j i i' (hij : M i j) (hi'j : M i' j) := hinj i i' j hij hi'j
  exact ⟨{
    nonneg := hε.le
    φ := matchingMap Uc Vc hUc (M := M) φ
    ψ := matchingMap Vc Uc hVc (M := fun j i => M i j) ψ
    φ_natural := matchingMap_natural Uc Vc hUc (M := M) φ hfun
      (fun i j hij _ _ h => intervalHom_natural k (hI i).2 (hJ j).2 hε (hclose i j hij) h)
    ψ_natural := matchingMap_natural Vc Uc hVc (M := fun j i => M i j) ψ hinj'
      (fun j i hij _ _ h => intervalHom_natural k (hJ j).2 (hI i).2 hε (hclose' j i hij) h)
    ψ_comp_φ := matchingMap_triangle Uc Vc hUc hVc (M := M) φ ψ hfun hinj' hε.le
      (fun i j hij => intervalHom_triangle k (hI i).2 (hJ j).2 hε (hclose i j hij))
      (fun i hi => intervalModule_map_eq_zero k (hI i).2 hδ' hε (hshortI i hi))
    φ_comp_ψ := matchingMap_triangle Vc Uc hVc hUc (M := fun j i => M i j) ψ φ hinj' hfun hε.le
      (fun j i hij => intervalHom_triangle k (hJ j).2 (hI i).2 hε (hclose' j i hij))
      (fun j hj => intervalModule_map_eq_zero k (hJ j).2 hδ' hε (hshortJ j hj))
  }⟩

end MathlibExt.Topology.PersistenceModuleWanted

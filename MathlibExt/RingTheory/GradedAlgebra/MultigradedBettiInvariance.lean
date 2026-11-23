/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti

/-!
# Invariance of multigraded Betti numbers under component presentation

This file proves that, for one fixed target grading and one fixed multigraded
free resolution, any two `MultigradedBaseChange` presentations give the same
`multigradedBettiNumber` at every multidegree and homological index.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 866--874. Those lines define `β^R_(i,α)(M)` as the vector-space
dimension of the `i`th homology of the degree-`α` component of `K ⊗ F` for a
graded free resolution `F` of `M`. Edge 3 exposes the component complex as a
certified `MultigradedBaseChange` package because Mathlib lacks a canonical
graded-subcomplex constructor; this edge eliminates that artificial choice.

Deliberately deferred (not claimed here): independence across different graded
free resolutions, existence of graded free resolutions, Poincaré
coefficient families, finite support, eventual vanishing, Hilbert syzygy
polynomiality, and Poincaré rationality. This file only proves fixed-resolution
presentation invariance of the component Betti number.

Main result:

* `MetaMathlibExt.multigradedBettiNumber_eq_of_baseChange`: two
  `MultigradedBaseChange` packages over the same resolution agree on
  `multigradedBettiNumber` for every `α` and `i`.
-/

@[expose] public section

namespace MetaMathlibExt

universe u

/-- **Betti numbers do not depend on the choice of base change data.** Let $K$ be a field,
let $R = K[x_1, \dots, x_n]$, and let $M$ be a $\mathbb{Z}^n$-graded $R$-module with a fixed
multigraded free resolution $P_\bullet \to M$. Any two choices of multigraded base change
data for $P_\bullet$ define the same multigraded Betti numbers, in every multidegree
$\alpha \in \mathbb{Z}^n$ and every homological index $i \in \mathbb{N}$.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 866--874. This covers only the fixed-resolution coherence step;
independence across resolutions, finite support, Poincaré polynomiality, and
Hilbert syzygy are deliberately not claimed here. -/
public theorem multigradedBettiNumber_eq_of_baseChange
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data₁ data₂ : MultigradedBaseChange targetGraded resolution ι res)
    (α : Fin n →₀ Int) (i : ℕ) :
    multigradedBettiNumber data₁ α i = multigradedBettiNumber data₂ α i := by
  have full : ∀ j : ℕ, ∃ e : ↥((data₁.comp α).X j) ≃ₗ[K] ↥((data₂.comp α).X j),
      ∀ x, ModuleCat.Hom.hom ((data₂.incl α).f j) (e x) =
        ModuleCat.Hom.hom ((data₁.incl α).f j) x := by
    intro j
    have hmem1 : ∀ x, ModuleCat.Hom.hom ((data₁.incl α).f j) x ∈
        baseChangedDegreePiece targetGraded resolution ι res j α := by
      intro x
      rw [← data₁.range_eq α j]
      exact ⟨x, rfl⟩
    have hmem2 : ∀ x, ModuleCat.Hom.hom ((data₂.incl α).f j) x ∈
        baseChangedDegreePiece targetGraded resolution ι res j α := by
      intro x
      rw [← data₂.range_eq α j]
      exact ⟨x, rfl⟩
    let ψ1 : ↥((data₁.comp α).X j) →ₗ[K]
        ↥(baseChangedDegreePiece targetGraded resolution ι res j α) :=
      LinearMap.codRestrict
        (baseChangedDegreePiece targetGraded resolution ι res j α)
        (ModuleCat.Hom.hom ((data₁.incl α).f j)) hmem1
    let ψ2 : ↥((data₂.comp α).X j) →ₗ[K]
        ↥(baseChangedDegreePiece targetGraded resolution ι res j α) :=
      LinearMap.codRestrict
        (baseChangedDegreePiece targetGraded resolution ι res j α)
        (ModuleCat.Hom.hom ((data₂.incl α).f j)) hmem2
    have hψ1 : ∀ x, (ψ1 x).val =
        ModuleCat.Hom.hom ((data₁.incl α).f j) x := fun x => rfl
    have hψ2 : ∀ x, (ψ2 x).val =
        ModuleCat.Hom.hom ((data₂.incl α).f j) x := fun x => rfl
    have hinj1 : Function.Injective ψ1 := by
      intro a b hab
      have h : ModuleCat.Hom.hom ((data₁.incl α).f j) a =
          ModuleCat.Hom.hom ((data₁.incl α).f j) b := by
        have hval := congrArg Subtype.val hab
        simpa [hψ1] using hval
      exact data₁.incl_injective α j h
    have hinj2 : Function.Injective ψ2 := by
      intro a b hab
      have h : ModuleCat.Hom.hom ((data₂.incl α).f j) a =
          ModuleCat.Hom.hom ((data₂.incl α).f j) b := by
        have hval := congrArg Subtype.val hab
        simpa [hψ2] using hval
      exact data₂.incl_injective α j h
    have hsurj1 : Function.Surjective ψ1 := by
      intro s
      have hs : s.val ∈
          LinearMap.range (ModuleCat.Hom.hom ((data₁.incl α).f j)) := by
        rw [data₁.range_eq α j]
        exact s.property
      obtain ⟨x, hx⟩ := hs
      refine Exists.intro x ?_
      apply Subtype.ext
      rw [hψ1]
      exact hx
    have hsurj2 : Function.Surjective ψ2 := by
      intro s
      have hs : s.val ∈
          LinearMap.range (ModuleCat.Hom.hom ((data₂.incl α).f j)) := by
        rw [data₂.range_eq α j]
        exact s.property
      obtain ⟨x, hx⟩ := hs
      refine Exists.intro x ?_
      apply Subtype.ext
      rw [hψ2]
      exact hx
    let e1 : ↥((data₁.comp α).X j) ≃ₗ[K]
        ↥(baseChangedDegreePiece targetGraded resolution ι res j α) :=
      LinearEquiv.ofBijective ψ1 ⟨hinj1, hsurj1⟩
    let e2 : ↥((data₂.comp α).X j) ≃ₗ[K]
        ↥(baseChangedDegreePiece targetGraded resolution ι res j α) :=
      LinearEquiv.ofBijective ψ2 ⟨hinj2, hsurj2⟩
    have h_e1_apply : ∀ y, e1 y = ψ1 y := fun y => rfl
    have h_e2_apply : ∀ y, e2 y = ψ2 y := fun y => rfl
    refine Exists.intro (e1.trans e2.symm) ?_
    intro x
    have hstep : ψ2 (e2.symm (e1 x)) = e1 x := by
      rw [← h_e2_apply (e2.symm (e1 x))]
      exact e2.apply_symm_apply (e1 x)
    have hEq1 : ModuleCat.Hom.hom ((data₂.incl α).f j) ((e1.trans e2.symm) x) =
        (ψ2 (e2.symm (e1 x))).val := by
      rw [hψ2 _]
      rfl
    have hEq2 : (ψ2 (e2.symm (e1 x))).val = (e1 x).val := by rw [hstep]
    have hEq3 : (e1 x).val =
        ModuleCat.Hom.hom ((data₁.incl α).f j) x := by
      rw [h_e1_apply x, hψ1 x]
    exact hEq1.trans (hEq2.trans hEq3)
  choose equiv key using full
  let iso : ∀ j, (data₁.comp α).X j ≅ (data₂.comp α).X j :=
    fun j =>
      { hom := ModuleCat.ofHom (equiv j).toLinearMap,
        inv := ModuleCat.ofHom (equiv j).symm.toLinearMap,
        hom_inv_id := by ext x; exact (equiv j).symm_apply_apply x,
        inv_hom_id := by ext x; exact (equiv j).apply_symm_apply x }
  have hIsoApply : ∀ (j : ℕ) (y), ModuleCat.Hom.hom (iso j).hom y = (equiv j) y :=
    fun j y => rfl
  have complexIso : data₁.comp α ≅ data₂.comp α := by
    refine HomologicalComplex.Hom.isoOfComponents iso ?_
    intro p q hRel
    ext x
    have hC1 := (data₁.incl α).comm' p q hRel
    have hC2 := (data₂.incl α).comm' p q hRel
    have eC1 : ModuleCat.Hom.hom ((data₁.incl α).f q)
          (ModuleCat.Hom.hom ((data₁.comp α).d p q) x) =
        ModuleCat.Hom.hom ((baseChangedComplex resolution).d p q)
          (ModuleCat.Hom.hom ((data₁.incl α).f p) x) :=
      (congrArg (fun f : (data₁.comp α).X p ⟶
        (baseChangedComplex resolution).X q => ModuleCat.Hom.hom f x) hC1).symm
    have eC2 : ModuleCat.Hom.hom ((data₂.incl α).f q)
          (ModuleCat.Hom.hom ((data₂.comp α).d p q) ((equiv p) x)) =
        ModuleCat.Hom.hom ((baseChangedComplex resolution).d p q)
          (ModuleCat.Hom.hom ((data₂.incl α).f p) ((equiv p) x)) :=
      (congrArg (fun f : (data₂.comp α).X p ⟶
        (baseChangedComplex resolution).X q =>
        ModuleCat.Hom.hom f ((equiv p) x)) hC2).symm
    have key_p : ModuleCat.Hom.hom ((data₂.incl α).f p) ((equiv p) x) =
        ModuleCat.Hom.hom ((data₁.incl α).f p) x := key p x
    have hEq : ModuleCat.Hom.hom ((data₂.incl α).f q)
          (ModuleCat.Hom.hom ((data₂.comp α).d p q) ((equiv p) x)) =
        ModuleCat.Hom.hom ((data₂.incl α).f q)
          ((equiv q) (ModuleCat.Hom.hom ((data₁.comp α).d p q) x)) := by
      rw [eC2, key_p, ← eC1, key q]
    have hPoint : ModuleCat.Hom.hom ((data₂.comp α).d p q) ((equiv p) x) =
        (equiv q) (ModuleCat.Hom.hom ((data₁.comp α).d p q) x) :=
      data₂.incl_injective α q hEq
    change ModuleCat.Hom.hom ((data₂.comp α).d p q)
        (ModuleCat.Hom.hom (iso p).hom x) =
      ModuleCat.Hom.hom (iso q).hom
        (ModuleCat.Hom.hom ((data₁.comp α).d p q) x)
    simp only [hIsoApply]
    exact hPoint
  have hH1 : HomologicalComplex.HasHomology (data₁.comp α) i :=
    data₁.hasHom α i
  have hH2 : HomologicalComplex.HasHomology (data₂.comp α) i :=
    data₂.hasHom α i
  have homIso : HomologicalComplex.homology (data₁.comp α) i ≅
      HomologicalComplex.homology (data₂.comp α) i := by
    letI := hH1
    letI := hH2
    exact HomologicalComplex.homologyMapIso complexIso i
  have linEquiv : ↥(HomologicalComplex.homology (data₁.comp α) i) ≃ₗ[K]
      ↥(HomologicalComplex.homology (data₂.comp α) i) :=
    CategoryTheory.Iso.toLinearEquiv homIso
  have hFin := LinearEquiv.finrank_eq linEquiv
  unfold multigradedBettiNumber
  exact hFin

end MetaMathlibExt

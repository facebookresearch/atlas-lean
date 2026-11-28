/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantSecondPage
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# The image filtration on total homology

Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and T = Tot(K). Extend
the horizontal subcomplexes G_a to EInt = ℤ ∪ {⊥,⊤}: bottom and negative finite stages are
zero, a nonnegative finite stage retains columns at most a, and the top stage is T.

For n ∈ ℕ, taking images of H_n(G_i) → H_n(T) gives an increasing filtration F_iH_n(T).
Negative finite stages are zero, stage n is exhaustive, and the map H_n(G_{n+1}) → H_n(T) is
an isomorphism. At n = p+q, the associated graded piece in column p is coker(F_{p−1}H_n(T) →
F_pH_n(T)), with its canonical short exact sequence.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. Let G_i be
the complete horizontal subcomplex of Tot(K), indexed by EInt = ℤ ∪ {⊥,⊤}; it is zero at
bottom and negative finite cuts, retains columns at most a at a ≥ 0, and equals Tot(K) at top.
Define the diagram EInt → C by i ↦ H_n(G_i), with each arrow i ≤ j mapped to homology of the
canonical inclusion G_i → G_j. -/
noncomputable def horizontalCompleteHomologyDiagram (n : ℕ) : EInt ⥤ C :=
  (horizontalCompleteTotalFiltration K).diagram ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C, write T = Tot(K), G_i for
its complete horizontal stage at i ∈ EInt, and ι_i : G_i → T for the inclusion. For n ∈ ℕ,
define H_n(G_i) → H_n(T) to be H_n(ι_i). This includes zero and top stages and uses the same
total complex and degree n at every filtration index. -/
noncomputable def horizontalCompleteHomologyToTotal (n : ℕ) (i : EInt) :
    (horizontalCompleteHomologyDiagram K n).obj i ⟶
      (K.total (ComplexShape.down ℕ)).homology n :=
  HomologicalComplex.homologyMap
    ((horizontalCompleteTotalFiltration K).ι.app i) n

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), n ∈ ℕ, and i ∈ EInt. The
map from the degree-n homology of the complete horizontal stage G_i to H_n(Tot(K)) equals
H_n(horizontalCompleteFilteredTotalToTotal K i). Thus the map used in the image filtration is
homology of the specified chain inclusion G_i → Tot(K). -/
theorem horizontalCompleteHomologyToTotal_eq (n : ℕ) (i : EInt) :
    horizontalCompleteHomologyToTotal K n i =
      HomologicalComplex.homologyMap
        (horizontalCompleteFilteredTotalToTotal K i) n :=
  rfl

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). For n ∈ ℕ, let h_i :
H_n(G_i) → H_n(Tot(K)) be the homology map of the complete horizontal stage inclusion. If f :
i → j is an arrow in EInt, the stage homology diagram satisfies H_n(G(f)) ≫ h_j = h_i. The
equality expresses compatibility with the transition G_i → G_j, for all finite and infinite
filtration indices. -/
theorem horizontalCompleteHomologyToTotal_naturality (n : ℕ)
    {i j : EInt} (f : i ⟶ j) :
    (horizontalCompleteHomologyDiagram K n).map f ≫
        horizontalCompleteHomologyToTotal K n j =
      horizontalCompleteHomologyToTotal K n i := by
  change HomologicalComplex.homologyMap
        ((horizontalCompleteTotalFiltration K).diagram.map f) n ≫
      HomologicalComplex.homologyMap
        ((horizontalCompleteTotalFiltration K).ι.app j) n =
    HomologicalComplex.homologyMap
      ((horizontalCompleteTotalFiltration K).ι.app i) n
  rw [← HomologicalComplex.homologyMap_comp]
  rw [(horizontalCompleteTotalFiltration K).ι.naturality f]
  simp

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. The objects
H_n(G_i) → H_n(Tot(K)), given by the complete horizontal stage inclusions for i ∈ EInt, form a
functor EInt → Over(H_n(Tot(K))). For i ≤ j its morphism is H_n(G_i → G_j), whose composite
with the map from H_n(G_j) to total homology equals the map from H_n(G_i). -/
noncomputable def horizontalCompleteHomologyOverDiagram (n : ℕ) :
    EInt ⥤ Over ((K.total (ComplexShape.down ℕ)).homology n) :=
  (horizontalCompleteHomologyDiagram K n).toOver _
    (horizontalCompleteHomologyToTotal K n)
    (horizontalCompleteHomologyToTotal_naturality K n)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. If G_i →
Tot(K) is the complete horizontal stage inclusion for i ∈ EInt, define F_iH_n(Tot(K)) =
im(H_n(G_i) → H_n(Tot(K))). The image inclusions are monomorphisms into the fixed
total-homology object, and the induced maps for i ≤ j make these subobjects an EInt-indexed
filtration. This is obtained by the image functor on the stage-homology diagram in the
overcategory. -/
noncomputable def horizontalTotalHomologyFiltration (n : ℕ) :
    CategoryTheory.Filtration
      ((K.total (ComplexShape.down ℕ)).homology n) EInt where
  toMonoOver := horizontalCompleteHomologyOverDiagram K n ⋙ MonoOver.image

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C, n ∈ ℕ, and i ∈ EInt, the
object at stage i of the induced total-homology filtration is exactly image(H_n(G_i →
Tot(K))). Here G_i is the complete horizontal stage and the arrow is its canonical inclusion.
The equality uses the chosen categorical image object. -/
theorem horizontalTotalHomologyFiltration_obj (n : ℕ) (i : EInt) :
    (horizontalTotalHomologyFiltration K n).obj i =
      image (horizontalCompleteHomologyToTotal K n i) :=
  rfl

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), n ∈ ℕ, and i ∈ EInt. The
structure morphism F_iH_n(Tot(K)) → H_n(Tot(K)) of the induced filtration equals
image.ι(H_n(G_i → Tot(K))). Thus each filtration stage is included by the canonical
monomorphism from the image of the complete-stage homology map. -/
theorem horizontalTotalHomologyFiltration_ι_app (n : ℕ) (i : EInt) :
    (horizontalTotalHomologyFiltration K n).ι.app i =
      image.ι (horizontalCompleteHomologyToTotal K n i) :=
  rfl

/-- Let K be a bicomplex of shape (down ℕ,down ℕ) in an abelian category C. For a ∈ ℤ with 0 ≤ a
and n ∈ ℕ with n ≤ a.toNat, the canonical map H_n(G_a) → H_n(Tot(K)) is epic, where G_a
retains the horizontal columns at most a. The condition ensures that the stage contains every
summand of total chain degree n; the conclusion concerns the map on degree-n homology. -/
theorem horizontalCompleteHomologyToTotal_epi_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    Epi (horizontalCompleteHomologyToTotal K n (a : EInt)) := by
  rw [horizontalCompleteHomologyToTotal_eq]
  have hmiddle : IsIso
      ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f n) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K a ha n h
  let _ := hmiddle
  have hnextmono : Mono
      ((horizontalCompleteFilteredTotalToTotal K (a : EInt)).f
        ((ComplexShape.down ℕ).next n)) := by
    change Mono (((if 0 ≤ a then
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat
    else horizontalCompleteFilteredTotalZeroMonoOver K).arrow).f
      ((ComplexShape.down ℕ).next n))
    rw [ite_eq_left ha]
    change Mono ((horizontalFilteredTotalComplexToTotal K a.toNat).f
      ((ComplexShape.down ℕ).next n))
    infer_instance
  have hcycles : IsIso (HomologicalComplex.cyclesMap
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)) n) := by
    exact ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
      ((HomologicalComplex.shortComplexFunctor C
        (ComplexShape.down ℕ) n).map
          (horizontalCompleteFilteredTotalToTotal K (a : EInt)))
      hmiddle hnextmono
  have hcyclesEpi : Epi (HomologicalComplex.cyclesMap
      (horizontalCompleteFilteredTotalToTotal K (a : EInt)) n) :=
    @IsIso.epi_of_iso _ _ _ _ _ hcycles
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap'
    ((HomologicalComplex.shortComplexFunctor C
      (ComplexShape.down ℕ) n).map
        (horizontalCompleteFilteredTotalToTotal K (a : EInt)))
    hcyclesEpi

/-- Let C be an abelian category and K a bicomplex of shape (down ℕ,down ℕ). If a ∈ ℤ satisfies 0
≤ a and n ∈ ℕ satisfies n ≤ a.toNat, the image-stage inclusion F_aH_n(Tot(K)) → H_n(Tot(K)) is
an isomorphism. Here F_a is the image of H_n(G_a) → H_n(Tot(K)), so the statement identifies
that image with all total homology. -/
theorem horizontalTotalHomologyFiltration_ι_app_isIso_of_nonneg
    (a : ℤ) (ha : 0 ≤ a) (n : ℕ) (h : n ≤ a.toNat) :
    IsIso ((horizontalTotalHomologyFiltration K n).ι.app (a : EInt)) := by
  rw [horizontalTotalHomologyFiltration_ι_app]
  let _ : Epi (horizontalCompleteHomologyToTotal K n (a : EInt)) :=
    horizontalCompleteHomologyToTotal_epi_of_nonneg K a ha n h
  have : Epi (image.ι
      (horizontalCompleteHomologyToTotal K n (a : EInt))) :=
    epi_image_of_epi _
  exact isIso_of_mono_of_epi _

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C and n ∈ ℕ, the inclusion
F_nH_n(Tot(K)) → H_n(Tot(K)) is an isomorphism. The index is the image of the integer n in
EInt, and F_n is the image of the homology map from the horizontal subcomplex retaining
columns at most n. Thus the degree-n image filtration is exhaustive by stage n. -/
theorem horizontalTotalHomologyFiltration_exhaustive (n : ℕ) :
    IsIso ((horizontalTotalHomologyFiltration K n).ι.app ((n : ℤ) : EInt)) :=
  horizontalTotalHomologyFiltration_ι_app_isIso_of_nonneg K (n : ℤ)
    (by omega) n (by simp)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and n ∈ ℕ. The canonical
map H_n(G_{n+1}) → H_n(Tot(K)) is an isomorphism, where G_{n+1} is the complete horizontal
stage at the finite integer n+1. This stage contains the total-complex terms in the three
degrees used to compute H_n, including the incoming degree n+1. -/
theorem horizontalCompleteHomologyToTotal_isIso_succ (n : ℕ) :
    IsIso (horizontalCompleteHomologyToTotal K n (((n : ℤ) + 1) : EInt)) := by
  rw [horizontalCompleteHomologyToTotal_eq,
    ← quasiIsoAt_iff_isIso_homologyMap]
  have htoNat : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [quasiIsoAt_iff'
    (horizontalCompleteFilteredTotalToTotal K (((n : ℤ) + 1) : EInt))
    ((ComplexShape.down ℕ).prev n) n ((ComplexShape.down ℕ).next n) rfl rfl]
  have hprev : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f ((ComplexShape.down ℕ).prev n)) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by rw [htoNat]; simp)
  have hmiddle : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f n) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by rw [htoNat]; omega)
  have hnext : IsIso ((horizontalCompleteFilteredTotalToTotal K
      (((n : ℤ) + 1) : EInt)).f ((ComplexShape.down ℕ).next n)) :=
    horizontalCompleteFilteredTotalToTotal_f_isIso_of_nonneg K
      ((n : ℤ) + 1) (by omega) _ (by
        rw [htoNat]
        cases n with
        | zero => simp
        | succ n => simp; omega)
  let φ := ((HomologicalComplex.shortComplexFunctor' C
    (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n) n
      ((ComplexShape.down ℕ).next n)).map
        (horizontalCompleteFilteredTotalToTotal K
          (((n : ℤ) + 1) : EInt)))
  have hτ₁ : IsIso φ.τ₁ := by
    dsimp [φ]
    exact hprev
  have hτ₂ : IsIso φ.τ₂ := by
    dsimp [φ]
    exact hmiddle
  have hτ₃ : IsIso φ.τ₃ := by
    dsimp [φ]
    exact hnext
  have hτ₁Epi : Epi φ.τ₁ := @IsIso.epi_of_iso _ _ _ _ _ hτ₁
  have hτ₃Mono : Mono φ.τ₃ := @IsIso.mono_of_iso _ _ _ _ _ hτ₃
  let _ := hτ₁Epi
  let _ := hτ₂
  let _ := hτ₃Mono
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- Let K be a bicomplex of shape (down ℕ,down ℕ) in an abelian category C. For a ∈ ℤ with a < 0
and any n ∈ ℕ, the stage F_aH_n(Tot(K)) is a zero object. The complete horizontal chain stage
G_a is zero at such a negative finite cut, and hence the image of its homology map into
H_n(Tot(K)) is zero. -/
theorem horizontalTotalHomologyFiltration_obj_isZero_of_neg
    (a : ℤ) (ha : a < 0) (n : ℕ) :
    IsZero ((horizontalTotalHomologyFiltration K n).obj (a : EInt)) := by
  rw [horizontalTotalHomologyFiltration_obj]
  apply IsZero.of_epi
    (factorThruImage (horizontalCompleteHomologyToTotal K n (a : EInt)))
  change IsZero
    ((horizontalCompleteFilteredTotalComplex K (a : EInt)).homology n)
  have hstage : IsZero
      ((horizontalCompleteFilteredTotalComplex K (a : EInt)).homology n) := by
    rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K a ha]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_zero _)
  exact hstage

/-- For p ∈ ℕ, the finite indices (p : ℤ)−1 and (p : ℤ), embedded in EInt = ℤ ∪ {⊥,⊤}, satisfy
(p−1 : EInt) ≤ (p : EInt). At p=0 the preceding index is the finite integer −1. This
inequality supplies the consecutive-stage filtration arrow. -/
theorem horizontalTotalHomologyPrevIndex_le (p : ℕ) :
    (((p : ℤ) - 1 : ℤ) : EInt) ≤ ((p : ℤ) : EInt) :=
  WithBotTop.coe_monotone (by omega)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. In total
degree n = p+q, define the map F_{p−1}H_n(Tot(K)) → F_pH_n(Tot(K)) induced by the inequality
(p : ℤ)−1 ≤ (p : ℤ) in EInt. Its composite with the stage-p inclusion into total homology is
the stage-(p−1) inclusion. For p=0 the source is the negative finite stage F_{−1}. -/
noncomputable def horizontalTotalHomologyFiltrationStepMap (p q : ℕ) :
    (horizontalTotalHomologyFiltration K (p + q)).obj
        (((p : ℤ) - 1 : ℤ) : EInt) ⟶
      (horizontalTotalHomologyFiltration K (p + q)).obj
        ((p : ℤ) : EInt) :=
  (((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
    (homOfLE (horizontalTotalHomologyPrevIndex_le p))).hom.left)

/-- For a bicomplex K of shape (down ℕ,down ℕ) in an abelian category C and p,q ∈ ℕ, the canonical
map F_{p−1}H_{p+q}(Tot(K)) → F_pH_{p+q}(Tot(K)) is a monomorphism. The stages are images of
the complete horizontal stage-homology maps into the same total-homology object, and the map
is the transition in their subobject filtration. -/
noncomputable instance horizontalTotalHomologyFiltrationStepMap_mono
    (p q : ℕ) :
    Mono (horizontalTotalHomologyFiltrationStepMap K p q) := by
  apply mono_of_mono_fac
    (MonoOver.w ((horizontalTotalHomologyFiltration K (p + q)).toMonoOver.map
      (homOfLE (horizontalTotalHomologyPrevIndex_le p))))

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. Define the
associated graded piece at bidegree (p,q) to be the cokernel of F_{p−1}H_{p+q}(Tot(K)) →
F_pH_{p+q}(Tot(K)). The index p−1 is computed in ℤ and embedded in EInt, so at p=0 the source
stage is F_{−1}=0. The object is a quotient of two consecutive image-filtration stages in the
fixed total degree p+q. -/
noncomputable abbrev horizontalTotalHomologyGradedPiece (p q : ℕ) : C :=
  cokernel (horizontalTotalHomologyFiltrationStepMap K p q)

/-- Let C be an abelian category, K a bicomplex of shape (down ℕ,down ℕ), and p,q ∈ ℕ. Put n = p+q
and s : F_{p−1}H_n(Tot(K)) → F_pH_n(Tot(K)) for the consecutive image-filtration inclusion.
Its cokernel sequence is short exact: 0 → F_{p−1}H_n(Tot(K)) → F_pH_n(Tot(K)) → coker(s) → 0.
The last object is the associated graded piece at (p,q), and its arrow is the canonical
cokernel projection. -/
theorem horizontalTotalHomologyFiltrationStepShortExact (p q : ℕ) :
    (ShortComplex.cokernelSequence
      (horizontalTotalHomologyFiltrationStepMap K p q)).ShortExact := by
  have hm : Mono ((ShortComplex.cokernelSequence
      (horizontalTotalHomologyFiltrationStepMap K p q)).f) := by
    change Mono (horizontalTotalHomologyFiltrationStepMap K p q)
    infer_instance
  let _ := hm
  exact { exact := ShortComplex.cokernelSequence_exact _ }

end HomologicalComplex₂

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.KernelTailBoundarySign
public import MathlibExt.Algebra.Homology.ChainComplexDegreeOneNormalization
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolution

/-!
# The degree-one sign of the kernel-tail comparison

Let `C`, `D` be abelian, with projective resolutions in `C`,
and `F : C → D` additive and preserving finite colimits. The
kernel-tail horseshoe boundary identifies degree-one derived
homology with the kernel of the mapped augmentation inclusion
with a minus sign.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
The degree-one horseshoe boundary, followed by the original degree-zero quotient comparison, is
the negative of the unsigned original kernel comparison.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`P` a projective resolution of `X`, and `F : C → D` additive
and preserving finite colimits. The degree-one-to-zero boundary
of the mapped kernel-tail horseshoe, followed by its degree-zero
comparison, is the negative of the canonical preserved-kernel-tail
map into `kernel(F(kernel.ι P.π₀))`. -/
theorem normalizationKernelTail_mappedBoundary_zero_sign {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] :
    ((normalizationKernelTailHorseshoe P).mapped_shortExact
      (normalizationKernelTailHorseshoeSpec P) F).δ 1 0 rfl ≫
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (normalizationKernelTail P).complex).homologyι 0 ≫
      (normalizationKernelTail P).fromLeftDerivedZero' F =
    -((ChainComplex.homologyOneIsoOfPreservedKernelTail F P.π).hom ≫
      kernel.ι (F.map (kernel.ι (P.π.f 0)))) := by
  let H := normalizationKernelTailHorseshoe P
  let sp := normalizationKernelTailHorseshoeSpec P
  let R := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let L := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (normalizationKernelTail P).complex
  let T := H.mapped F
  let M := T.X₂
  let hT := H.mapped_shortExact sp F
  let x : R.cycles 1 ⟶ F.obj (P.complex.X 1) := R.iCycles 1
  let x₂ := x ≫ F.map (biprod.inr :
    P.complex.X 1 ⟶ (normalizationKernelTail P).complex.X 1 ⊞ P.complex.X 1)
  let y := -(x ≫ F.map (normalizationKernelTailXIso P 0).inv)
  have hx : x ≫ R.d 1 0 = 0 := R.iCycles_d _ _
  have hx₂ : x₂ ≫ T.g.f 1 = x := by
    change (x ≫ F.map biprod.inr) ≫ F.map biprod.snd = x
    rw [Category.assoc, ← F.map_comp, biprod.inr_snd, F.map_id]
    exact Category.comp_id x
  have hy : y ≫ T.f.f 0 = x₂ ≫ M.d 1 0 := by
    change y ≫ F.map biprod.inl =
      (x ≫ F.map biprod.inr) ≫ F.map ((normalizationMiddleComplex P).d 1 0)
    rw [normalizationMiddleComplex_d]
    have hb := normalizationMappedBiprod_inr_boundary F
      ((normalizationKernelTail P).complex.d 1 0) (normalizationCross P 0)
      (P.complex.d 1 0) x hx
    dsimp only [normalizationMiddleDifferential]
    rw [Category.assoc, hb]
    simp only [normalizationCross, normalizationCrossSign, zero_add, pow_one,
      neg_one_zsmul, F.map_neg, comp_neg, y, neg_comp, Category.assoc]
  have hyL : y ≫ L.d 0 0 = 0 := by
    rw [L.shape 0 0 (by simp), comp_zero]
  have hδ := hT.δ_eq 1 0 rfl x hx x₂ hx₂ y hy 0 (by simp)
  have h := congrArg (fun q => q ≫ L.homologyι 0 ≫
    (normalizationKernelTail P).fromLeftDerivedZero' F) hδ
  have hxid : R.liftCycles x 0 (by simp) hx = 𝟙 (R.cycles 1) := by
    apply (cancel_mono (R.iCycles 1)).1
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
    rfl
  change (R.liftCycles x 0 (by simp) hx ≫ R.homologyπ 1 ≫ hT.δ 1 0 rfl) ≫
      L.homologyι 0 ≫ (normalizationKernelTail P).fromLeftDerivedZero' F =
    (L.liftCycles y 0 (by simp) hyL ≫ L.homologyπ 0) ≫ L.homologyι 0 ≫
      (normalizationKernelTail P).fromLeftDerivedZero' F at h
  rw [hxid, Category.id_comp] at h
  simp only [Category.assoc, HomologicalComplex.homology_π_ι_assoc,
    HomologicalComplex.liftCycles_i_assoc] at h
  rw [pOpcycles_comp_fromLeftDerivedZero'] at h
  have hyq : y ≫ F.map ((normalizationKernelTail P).π.f 0) =
      -(x ≫ F.map (kernel.lift (P.π.f 0) (P.complex.d 1 0)
        P.complex_d_comp_π_f_zero)) := by
    rw [normalizationKernelTail_π_f_zero]
    have h₀ : (normalizationKernelTailXIso P 0).inv = 𝟙 (P.complex.X 1) := rfl
    dsimp only [y]
    rw [h₀, F.map_id, Category.comp_id, neg_comp]
  have hc := ChainComplex.homologyπ_homologyOneIsoOfPreservedKernelTail_hom_ι F P.π
  have hn := congrArg (fun q => -q) hc
  have hf := (h.trans hyq).trans hn.symm
  change hT.δ 1 0 rfl ≫ L.homologyι 0 ≫ (normalizationKernelTail P).fromLeftDerivedZero' F =
    -((ChainComplex.homologyOneIsoOfPreservedKernelTail F P.π).hom ≫
      kernel.ι (F.map (kernel.ι (P.π.f 0))))
  apply (cancel_epi (R.homologyπ 1)).1
  simpa only [Category.assoc, comp_neg] using hf

variable [HasProjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
The SAME derived boundary retains the degree-one minus sign.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`P` a projective resolution of `X`, and `F : C → D` additive
and preserving finite colimits. The native left-derived boundary
for `kernel(P.π₀) → P⁰ → X`, followed by the degree-zero
comparison, is the negative preserved-kernel-tail map from `L₁F(X)`. -/
theorem normalizationKernelTail_nativeBoundary_zero_sign {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] :
    (P.isoLeftDerivedObj F 1).inv ≫
      LeftDerivedDelta.LDdelta F 0 (ShortComplex.kernelSequence (P.π.f 0))
        (normalizationKernelSequence_shortExact P) ≫
      F.fromLeftDerivedZero.app (kernel (P.π.f 0)) =
    -((ChainComplex.homologyOneIsoOfPreservedKernelTail F P.π).hom ≫
      kernel.ι (F.map (kernel.ι (P.π.f 0)))) := by
  rw [← (normalizationKernelTailHorseshoe P).delta_eq_native
    (normalizationKernelTailHorseshoeSpec P) F 0]
  dsimp only [HorseshoeData.delta, normalizationKernelTailHorseshoe,
    ShortComplex.kernelSequence]
  rw [(normalizationKernelTail P).fromLeftDerivedZero_eq F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Iso.inv_hom_id_assoc (P.isoLeftDerivedObj F 1) _).trans
    (normalizationKernelTail_mappedBoundary_zero_sign P F)

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
Under the original kernel iso the retained degree-one comparison has sign -1.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and `P`
a projective resolution whose terms are `F`-acyclic. The
degree-one derived kernel comparison composed with
`P.isoLeftDerivedObj F 1` inverse equals the negative canonical
preserved-kernel-tail homology comparison. -/
theorem normalizationAcyclicProjective_one_kernel {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (P.complex.X q))) :
    (P.isoLeftDerivedObj F 1).inv ≫
      (F.leftDerivedOneIsoKernel
        ⟨ShortComplex.kernelSequence (P.π.f 0), normalizationKernelSequence_shortExact P⟩
        (hP 0 0)).hom =
      -(ChainComplex.homologyOneIsoOfPreservedKernelTail F P.π).hom := by
  apply (cancel_mono (kernel.ι (F.map (kernel.ι (P.π.f 0))))).1
  simp only [neg_comp, Category.assoc]
  have hc := F.leftDerivedOneIsoKernel_hom_ι
    ⟨ShortComplex.kernelSequence (P.π.f 0), normalizationKernelSequence_shortExact P⟩ (hP 0 0)
  exact (congrArg (fun q => (P.isoLeftDerivedObj F 1).inv ≫ q) hc).trans
    (normalizationKernelTail_nativeBoundary_zero_sign P F)

set_option backward.isDefEq.respectTransparency false in
/- Proof implementation note.
In degree one the retained acyclic comparison is the negative of the SAME projective comparison.
-/

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive and preserving finite colimits, and `P`
a projective resolution with `L_(n+1)F(P^q)=0` for all `q,n`.
The degree-one acyclic comparison has forward map equal to
the negative of the canonical projective-resolution comparison. -/
theorem normalizationAcyclicProjective_one {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (P.complex.X q))) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP 1).hom =
      -(P.isoLeftDerivedObj F 1).hom := by
  apply (cancel_epi (P.isoLeftDerivedObj F 1).inv).1
  unfold Functor.leftDerivedObjIsoHomologyOfAcyclicResolution
  change (P.isoLeftDerivedObj F 1).inv ≫
    ((F.leftDerivedOneIsoKernel
      ⟨ShortComplex.kernelSequence (P.π.f 0), normalizationKernelSequence_shortExact P⟩
      (hP 0 0)).hom ≫ (ChainComplex.homologyOneIsoOfPreservedKernelTail F P.π).inv) =
    (P.isoLeftDerivedObj F 1).inv ≫ (-(P.isoLeftDerivedObj F 1).hom)
  rw [← Category.assoc, normalizationAcyclicProjective_one_kernel]
  simp only [neg_comp, comp_neg, Iso.hom_inv_id, Iso.inv_hom_id]

end CategoryTheory.ProjectiveResolution

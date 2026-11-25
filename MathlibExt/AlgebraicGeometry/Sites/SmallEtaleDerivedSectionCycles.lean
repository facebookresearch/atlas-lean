/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedHomSectionsComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeExtBoundary
public import MathlibExt.CategoryTheory.Abelian.Ext.CycleClassTransport
public import Mathlib.Algebra.Category.Grp.EpiMono

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- The actual section cycle of an original integral-generator resolution cocycle. -/
def sectionsCycle (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    let K := ((Γ.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution Q).cocomplex
    (K.sc q).g.hom.ker := by
  refine ⟨integralHomSections.{u, w} X _ f, ?_⟩
  change (Γ.{u, w} X).map
    ((injectiveResolution Q).cocomplex.d q ((ComplexShape.up ℕ).next q))
      (integralHomSections.{u, w} X _ f) = 0
  rw [ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)]
  rw [← integralHomSections_naturality, hf, map_zero]

/-- The same section-homology projection followed by the existing derived comparison. -/
def cycleClass (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    ((Γ.{u, w} X).rightDerived q).obj Q :=
  let R := injectiveResolution Q
  let K := ((Γ.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  (R.isoRightDerivedObj (Γ.{u, w} X) q).inv
    ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv (sectionsCycle.{u, w} X Q q f hf)))

/-- Evaluate the original comparison through the same size and lifted comparison. -/
theorem originalComparison_apply
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (ξ : Sheaf.H.{max u w, max u w, u, u + 1} Q q) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    originalComparison.{u, w} X Q q ξ =
      (((largeComparisonIso.{u, w} X q).app Q).hom
        (extSizeEquiv.{u, w} X Q q ξ)).down := by
  let : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  rfl

/-- The lifted comparison sends a resolution representative to its actual section class. -/
theorem largeComparison_extMk
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    letI : HasExt.{max (u + 1) w}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
    ((largeComparisonIso.{u, w} X q).app Q).hom
        ((injectiveResolution Q).extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1}
          f (q + 1) rfl hf) =
      (ULift.up (cycleClass.{u, w} X Q q f hf) :
        AddCommGrpCat.uliftFunctor.{u + 1, max u w}.obj
          (((Γ.{u, w} X).rightDerived q).obj Q)) := by
  let : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  let R := injectiveResolution Q
  let G := Γ.{u, w} X
  let z := sectionsCycle.{u, w} X Q q f hf
  have hTransport := Abelian.rightDerivedCoyonedaCompIso_inv_extMk_cycleClass.{
    (max u w) + 1, max u w, u + 1} G (integralSheaf.{u, w} X) Q q
    (homLiftIso.{u, w} X).hom f hf z (by rfl)
  have h := (largeComparison_apply.{u, w} X Q q
    (R.extMk.{max (u + 1) w, max (u + 1) w, (max u w) + 1}
      f (q + 1) rfl hf)).trans hTransport
  exact h.trans (by rfl)

-- This retains the existing budget for the original representative predicate.
/-- The comparison constructed through the same Hom/section isomorphism sends
every original Ext representative, including zero, to its literal section class. -/
theorem originalComparison_extMk (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (q : ℕ) (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Q).cocomplex.d q (q + 1) = 0) :
    let A : AddCommGrpCat.{max u w} := ((Γ.{u, w} X).rightDerived q).obj Q
    let e : Sheaf.H.{max u w, max u w, u, u + 1} Q q ≃+ A :=
      originalComparison.{u, w} X Q q
    let x : Sheaf.H.{max u w, max u w, u, u + 1} Q q :=
      (injectiveResolution Q).extMk.{max u w, max (u + 1) w, (max u w) + 1}
        f (q + 1) rfl hf
    e x = (cycleClass.{u, w} X Q q f hf : A) := by
  let : HasExt.{max (u + 1) w}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) := largeExt.{u, w} X
  let R := injectiveResolution Q
  let U := AddCommGrpCat.uliftFunctor.{u + 1, max u w}
  let G := Γ.{u, w} X
  have hSize := extSizeEquiv_extMk.{u, w} X Q q f hf
  have hResult : ((largeComparisonIso.{u, w} X q).app Q).hom
        (extSizeEquiv.{u, w} X Q q
          (R.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf)) =
      (ULift.up (cycleClass.{u, w} X Q q f hf) : U.obj ((G.rightDerived q).obj Q)) :=
    (congrArg (fun ξ : Abelian.Ext.{max (u + 1) w} (integralSheaf.{u, w} X) Q q =>
       ((largeComparisonIso.{u, w} X q).app Q).hom ξ) hSize).trans
      (largeComparison_extMk.{u, w} X Q q f hf)
  exact (originalComparison_apply.{u, w} X Q q
    (R.extMk.{max u w, max (u + 1) w, (max u w) + 1} f (q + 1) rfl hf)).trans
      (congrArg ULift.down hResult)

/-- Positive cycle classes are the SAME existing three-term section presentation. -/
theorem cycleClass_positive (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (n : ℕ) (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0)
    (z : (positiveShort.{u, w} X Q n).g.hom.ker)
    (hz : z.val = integralHomSections.{u, w} X _ f) :
    cycleClass.{u, w} X Q (n + 1) f hf = positiveCycleClass.{u, w} X Q n z := by
  let R := injectiveResolution Q
  let K := ((Γ.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let E := K.isoSc' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))
  obtain ⟨z₀, hvalue, hclass⟩ := ShortComplex.ab_cycle_transport_inv E z
  have heq : sectionsCycle.{u, w} X Q (n + 1) f hf = z₀ := by
    apply Subtype.ext
    change integralHomSections.{u, w} X _ f = z₀.val
    exact hz.symm.trans hvalue.symm
  change (R.isoRightDerivedObj (Γ.{u, w} X) (n + 1)).inv
    ((K.sc (n + 1)).homologyπ ((K.sc (n + 1)).abCyclesIso.inv _)) = _
  rw [heq]
  exact congrArg (R.isoRightDerivedObj (Γ.{u, w} X) (n + 1)).inv hclass

/-- Every original positive representative follows the same canonical Γ family. -/
theorem canonicalEquiv_extMk_positive
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0) :
    CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q (n + 1)
      ((injectiveResolution Q).extMk f (n + 2) rfl hf) =
        cycleClass.{u, w} X Q (n + 1) f hf := by
  obtain ⟨z, hz, heq⟩ := CanonicalLongExactSequence.canonicalEquiv_representative.{u, w}
    X Q n f hf
  exact heq.trans (cycleClass_positive.{u, w} X Q n f hf z hz).symm

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

/-- The genuine size/Hom/section comparison is exactly the SAME existing
canonical positive family, by the original resolution representative equations. -/
theorem originalComparison_positive
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) (n : ℕ) :
    originalComparison.{u, w} X Q (n + 1) =
      CanonicalLongExactSequence.canonicalEquiv.{u, w} X Q (n + 1) := by
  apply DFunLike.coe_injective
  funext x
  obtain ⟨f, hf, hx⟩ := (injectiveResolution Q).extMk_surjective
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w})
    (X := integralSheaf.{u, w} X) (α := x) (n + 2) rfl
  rw [← hx]
  exact (originalComparison_extMk.{u, w} X Q (n + 1) f hf).trans
    (canonicalEquiv_extMk_positive.{u, w} X Q n f hf).symm

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- The mapped section/differential/retraction has exactly the original
integral-generator value; no comparison or connecting-square premise is used. -/
theorem mappedConnectingRepresentative_sections
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (H : Functor.RightDerived.HorseshoeData S hS) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ H.res₃.cocomplex.X q)
    (x : (H.mapped (Γ.{u, w} X)).X₃.cycles q)
    (hx : (H.mapped (Γ.{u, w} X)).X₃.iCycles q x = integralHomSections.{u, w} X _ f) :
    HomologicalComplex.splitConnectingRepresentative (H.mapped (Γ.{u, w} X))
      (H.mappedSplitting (Γ.{u, w} X)) q ((H.mapped (Γ.{u, w} X)).X₃.iCycles q) x =
        integralHomSections.{u, w} X _ (H.originalConnectingRepresentative q f) := by
  change (Γ.{u, w} X).map (H.split (q + 1)).r
    ((Γ.{u, w} X).map (H.res₂.cocomplex.d q (q + 1))
      ((Γ.{u, w} X).map (H.split q).s ((H.mapped (Γ.{u, w} X)).X₃.iCycles q x))) = _
  have h₁ := integralHomSections_naturality.{u, w} X f (H.split q).s
  have h₂ := integralHomSections_naturality.{u, w} X (f ≫ (H.split q).s)
    (H.res₂.cocomplex.d q (q + 1))
  have h₃ := integralHomSections_naturality.{u, w} X
    ((f ≫ (H.split q).s) ≫ H.res₂.cocomplex.d q (q + 1)) (H.split (q + 1)).r
  exact (congrArg (fun t => (Γ.{u, w} X).map (H.split (q + 1)).r
    ((Γ.{u, w} X).map (H.res₂.cocomplex.d q (q + 1))
      ((Γ.{u, w} X).map (H.split q).s t))) hx).trans
    ((congrArg (fun t => (Γ.{u, w} X).map (H.split (q + 1)).r
      ((Γ.{u, w} X).map (H.res₂.cocomplex.d q (q + 1)) t)) h₁.symm).trans
      ((congrArg (fun t => (Γ.{u, w} X).map (H.split (q + 1)).r t) h₂.symm).trans
        h₃.symm))

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge
variable (X : Scheme.{u})

set_option backward.isDefEq.respectTransparency false in
/-- On every original integral-generator cycle, the SAME canonical Γ connector
is the actual section/differential/retraction class in its chosen endpoint resolutions. -/
theorem canonicalConnecting_cycleClass
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
    (hS : S.ShortExact) (q : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution S.X₃).cocomplex.X q)
    (hf : f ≫ (injectiveResolution S.X₃).cocomplex.d q (q + 1) = 0) :
    let H := Functor.RightDerived.HorseshoeData.ofEndpoints S hS
      (injectiveResolution S.X₁) (injectiveResolution S.X₃)
    (Functor.rightDerivedConnecting (Γ.{u, w} X) q).app ⟨S, hS⟩
      (cycleClass.{u, w} X S.X₃ q f hf) =
        cycleClass.{u, w} X S.X₁ (q + 1) (H.originalConnectingRepresentative q f)
          (H.originalConnectingRepresentative_cycle q f hf) := by
  let H := Functor.RightDerived.HorseshoeData.ofEndpoints S hS
    (injectiveResolution S.X₁) (injectiveResolution S.X₃)
  let K₁ := (H.mapped (Γ.{u, w} X)).X₁
  let K₃ := (H.mapped (Γ.{u, w} X)).X₃
  let z₃ := sectionsCycle.{u, w} X S.X₃ q f hf
  let c₃ := (K₃.sc q).abCyclesIso.inv z₃
  let a := H.originalConnectingRepresentative q f
  let ha := H.originalConnectingRepresentative_cycle q f hf
  let z₁ := sectionsCycle.{u, w} X S.X₁ (q + 1) a ha
  let c₁ := (K₁.sc (q + 1)).abCyclesIso.inv z₁
  let r := HomologicalComplex.splitConnectingRepresentative (H.mapped (Γ.{u, w} X))
    (H.mappedSplitting (Γ.{u, w} X)) q (K₃.iCycles q)
  let hr := HomologicalComplex.splitConnectingRepresentative_cycle
    (H.mapped (Γ.{u, w} X)) (H.mappedSplitting (Γ.{u, w} X)) q (K₃.iCycles q)
    (K₃.iCycles_d q (q + 1))
  let l := K₁.liftCycles r (q + 2)
    (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)) hr
  have hx : K₃.iCycles q c₃ = integralHomSections.{u, w} X _ f :=
    (K₃.sc q).abCyclesIso_inv_apply_iCycles z₃
  have hl : l c₃ = c₁ := by
    apply (AddCommGrpCat.mono_iff_injective (K₁.iCycles (q + 1))).1 inferInstance
    calc
      K₁.iCycles (q + 1) (l c₃) = r c₃ :=
        ConcreteCategory.congr_hom
          (K₁.liftCycles_i r (q + 2)
            (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)) hr) c₃
      _ = integralHomSections.{u, w} X _ a :=
        mappedConnectingRepresentative_sections.{u, w} X S hS H q f c₃ hx
      _ = K₁.iCycles (q + 1) c₁ :=
        ((K₁.sc (q + 1)).abCyclesIso_inv_apply_iCycles z₁).symm
  have hδ : (H.mapped_shortExact (Γ.{u, w} X)).δ q (q + 1) rfl
      ((K₃.sc q).homologyπ c₃) = (K₁.sc (q + 1)).homologyπ (l c₃) :=
    ConcreteCategory.congr_hom (H.mapped_delta_cycles (Γ.{u, w} X) q) c₃
  have hR : (H.res₃.isoRightDerivedObj (Γ.{u, w} X) q).hom
      (cycleClass.{u, w} X S.X₃ q f hf) = (K₃.sc q).homologyπ c₃ := by
    change (H.res₃.isoRightDerivedObj (Γ.{u, w} X) q).hom
      ((H.res₃.isoRightDerivedObj (Γ.{u, w} X) q).inv ((K₃.sc q).homologyπ c₃)) = _
    exact (H.res₃.isoRightDerivedObj (Γ.{u, w} X) q).addCommGroupIsoToAddEquiv.apply_symm_apply _
  change (H.res₁.isoRightDerivedObj (Γ.{u, w} X) (q + 1)).inv
    ((H.mapped_shortExact (Γ.{u, w} X)).δ q (q + 1) rfl
      ((H.res₃.isoRightDerivedObj (Γ.{u, w} X) q).hom
        (cycleClass.{u, w} X S.X₃ q f hf))) = _
  rw [hR, hδ, hl]
  rfl

end AlgebraicGeometry.Scheme.DerivedSections.OriginalGammaBridge

end

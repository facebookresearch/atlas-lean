/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientWaldhausen
public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicCycles
public import MathlibExt.Algebra.Homology.ShortComplex.MiddleQuasiIso
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import MathlibExt.CategoryTheory.Waldhausen.Fibration.TrivialCofibration

/-!
# Exact rows of the original bounded ambient cofiber sequences

The original source cofibration and its actual chosen zero pushout retain
both original legs. The pointwise source pushouts earn the actual cokernel
UP and source admissible exact row. The specified exact ambient functor
therefore maps the same original raw row to a short exact row.

The extension comparisons use the same whole original row maps and ambient
raw quasi-isomorphisms. Source homology, global source limits, weak
idempotent completeness and row/extension outcomes are absent. All four
source and ambient object and Hom universes remain independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CochainComplex.Bounded

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive] [F.IsExact]

omit [F.IsExact] in
/-- The same actual chosen source quotient is the cokernel on every original component. -/
def ambientCofiberTermIsColimit {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) (j : ℤ) :
    letI := ambientWaldhausenCategory F
    IsColimit (CokernelCofork.ofπ (f := i.hom.f j) (p.hom.f j) (by
      exact congrArg (fun t : X ⟶ Z => t.hom.f j) hSeq.comp_eq_zero)) := by
  let _ := ambientWaldhausenCategory F
  have hi := hSeq.1
  have hP : IsPushout (0 : X ⟶ (0 : Bounded E)) i (0 : (0 : Bounded E) ⟶ Z) p := by
    obtain ⟨h, q, hP⟩ := hSeq.2
    have hh : h = 0 := (isZero_zero (Bounded E)).eq_of_tgt _ _
    have hq : q = 0 := (isZero_zero (Bounded E)).eq_of_src _ _
    simpa only [hh, hq] using hP
  have hTerm := (admissiblePushout_term E ((ambient_isCofibration_iff F i).mp hi) hP.flip j).flip
  have hZero : IsZero ((0 : Bounded E).obj.X j) :=
    (HomologicalComplex.eval E (.up ℤ) j).map_isZero
      ((ι E).map_isZero (isZero_zero (Bounded E)))
  refine CokernelCofork.IsColimit.ofπ (p.hom.f j) _
    (fun {W} g hg => hTerm.desc 0 g (by rw [comp_zero, hg])) ?_ ?_
  · intro W g hg
    exact hTerm.inr_desc 0 g (by rw [comp_zero, hg])
  · intro W g hg m hm
    apply hTerm.hom_ext
    · exact hZero.eq_of_src _ _
    · rw [hm, hTerm.inr_desc]

omit [F.IsExact] in
/-- Each actual original cofiber row is an admissible exact row in the original source. -/
theorem ambientCofiberTerm_isAdmissibleExact {X Y Z : Bounded E}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) (j : ℤ) :
    letI := ambientWaldhausenCategory F
    IsAdmissibleExact (ShortComplex.mk (i.hom.f j) (p.hom.f j) (by
      exact congrArg (fun t : X ⟶ Z => t.hom.f j) hSeq.comp_eq_zero)) := by
  let _ := ambientWaldhausenCategory F
  exact isAdmissibleExact_of_isAdmissibleMono_isColimit
    ((ambient_isCofibration_iff F i).mp hSeq.1 j) (ambientCofiberTermIsColimit F i p hSeq j)

omit [F.IsExact] in
/-- The same original bounded row is projected through the literal original bounded inclusion. -/
abbrev ambientCofiberRawRow {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    ShortComplex (CochainComplex E ℤ) := by
  let _ := ambientWaldhausenCategory F
  exact ShortComplex.mk i.hom p.hom
    (congrArg (fun t : X ⟶ Z => t.hom) hSeq.comp_eq_zero)

/-- The specified exact functor maps the same actual original cofiber row to a short exact row. -/
theorem ambientCofiberRawRow_map_shortExact {X Y Z : Bounded E}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    ((ambientCofiberRawRow F i p hSeq).map (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  let _ := ambientWaldhausenCategory F
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  change ((ShortComplex.mk (i.hom.f j) (p.hom.f j)
    (congrArg (fun t : X ⟶ Z => t.hom.f j) hSeq.comp_eq_zero)).map F).ShortExact
  exact F.map_admissibleExact _ (ambientCofiberTerm_isAdmissibleExact F i p hSeq j)

/-- Any original bounded row identified as a cofiber sequence maps to the same actual short exact row. -/
theorem ambientShortComplex_map_shortExact (S : ShortComplex (Bounded E))
    (hS : letI := ambientWaldhausenCategory F; IsCofiberSequence S.f S.g) :
    (S.map (ι E ⋙ F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  ambientCofiberRawRow_map_shortExact F S.f S.g hS

/-- The same whole original cofiber-row comparison has extension for the actual ambient weak model. -/
theorem ambientCofiber_extension {S T : ShortComplex (Bounded E)} (φ : S ⟶ T)
    (hS : letI := ambientWaldhausenCategory F; IsCofiberSequence S.f S.g)
    (hT : letI := ambientWaldhausenCategory F; IsCofiberSequence T.f T.g) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence φ.τ₁ → IsWeakEquivalence φ.τ₃ → IsWeakEquivalence φ.τ₂ := by
  let _ := ambientWaldhausenCategory F
  intro hLeft hRight
  apply (ambient_isWeakEquivalence_iff F _).mpr
  let J := ι E ⋙ F.mapHomologicalComplex (.up ℤ)
  let ψ := J.mapShortComplex.map φ
  have hLeftRaw : QuasiIso ψ.τ₁ := (ambient_isWeakEquivalence_iff F _).mp hLeft
  have hRightRaw : QuasiIso ψ.τ₃ := (ambient_isWeakEquivalence_iff F _).mp hRight
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ ψ
    (ambientShortComplex_map_shortExact F S hS)
    (ambientShortComplex_map_shortExact F T hT) hLeftRaw hRightRaw

/-- The original trivial cofibration is exactly one whose same chosen quotient is ambient-acyclic. -/
theorem ambientCofiber_isWeakEquivalence_iff_quotient_acyclic {X Y Z : Bounded E}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence i ↔ ((F.mapHomologicalComplex (.up ℤ)).obj Z.obj).Acyclic := by
  let _ := ambientWaldhausenCategory F
  exact (ambient_isWeakEquivalence_iff F i).trans
    ((ambientCofiberRawRow_map_shortExact F i p hSeq).quasiIso_f_iff)

/-- The actual bounded ambient exact rows instantiate the original generic extension axiom. -/
theorem ambientWaldhausen_extension :
    letI := ambientWaldhausenCategory F
    WaldhausenExtensionAxiom (C := Bounded E) := by
  let _ := ambientWaldhausenCategory F
  constructor
  intro X Y Q X' Y' Q' i q i' q' hS hT a b c wi wq ha hc
  let S : ShortComplex (Bounded E) := ShortComplex.mk i q hS.comp_eq_zero
  let T : ShortComplex (Bounded E) := ShortComplex.mk i' q' hT.comp_eq_zero
  let φ : S ⟶ T := ShortComplex.homMk a b c wi.symm wq.symm
  exact ambientCofiber_extension F φ hS hT ha hc

/-- The canonical generic quotient theorem retains the same actual bounded cofiber quotient. -/
theorem ambientCofiber_isWeakEquivalence_iff_canonical_acyclic {X Y Q : Bounded E}
    (i : X ⟶ Y) (q : Y ⟶ Q)
    (hS : letI := ambientWaldhausenCategory F; IsCofiberSequence i q) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence i ↔ WaldhausenCategoryWithoutGluing.acyclicObjects Q := by
  let _ := ambientWaldhausenCategory F
  exact hS.isWeakEquivalence_iff_acyclic
    (ambientWaldhausen_gluing F) (ambientWaldhausen_extension F)

variable [F.Full] [F.Faithful] [F.ReflectsAdmissibleExact]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

include hKernelClosure in
/-- The same original quotient belongs to the actual all-degree source acyclic-cycle category. -/
theorem ambientCofiber_isWeakEquivalence_iff_quotient_admissibleData {X Y Z : Bounded E}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence i ↔ Nonempty (AmbientCycles.AdmissibleAcyclicData Z) := by
  let _ := ambientWaldhausenCategory F
  exact (ambientCofiber_isWeakEquivalence_iff_quotient_acyclic F i p hSeq).trans
    (AmbientCycles.ambient_acyclic_iff_admissibleData F Z hKernelClosure)

end CochainComplex.Bounded

end

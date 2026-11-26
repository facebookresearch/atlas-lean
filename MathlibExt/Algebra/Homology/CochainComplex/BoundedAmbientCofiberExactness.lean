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
# Ambient exactness of bounded cofiber rows

Let E be preadditive Quillen exact with a zero object and binary biproducts,
and F:E → A additive with A abelian.
A cofiber sequence X —i→ Y —p→ Z of bounded complexes has a cokernel
projection p_j in every degree and an admissible exact component row.

When F is exact, the underlying cochain row maps to a short exact sequence
of ambient complexes. Thus maps of cofiber sequences satisfy the extension
axiom for F-detected quasi-isomorphisms, and i is an ambient weak equivalence
exactly when F(Z) is acyclic. With full faithfulness, reflection and
essential-image kernel closure, this is also equivalent to all-degree
admissible cycle data on Z. The source and ambient universes are independent.
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
/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences.

For a cofiber sequence X —i→ Y —p→ Z, each component p_j:Y^j → Z^j is a cokernel of i_j:X^j → Y^j. -/
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
/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences.

Every component row X^j → Y^j → Z^j of a cofiber sequence is admissible exact in E. -/
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
/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences.

The underlying short complex of integer cochains associated to a bounded cofiber sequence has its original maps i and p. -/
abbrev ambientCofiberRawRow {X Y Z : Bounded E} (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    ShortComplex (CochainComplex E ℤ) := by
  let _ := ambientWaldhausenCategory F
  exact ShortComplex.mk i.hom p.hom
    (congrArg (fun t : X ⟶ Z => t.hom) hSeq.comp_eq_zero)

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

The underlying row of any bounded cofiber sequence becomes short exact after termwise application of F. -/
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

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

A short complex of bounded objects whose two maps form a cofiber sequence becomes a short exact sequence of ambient cochain complexes under F. -/
theorem ambientShortComplex_map_shortExact (S : ShortComplex (Bounded E))
    (hS : letI := ambientWaldhausenCategory F; IsCofiberSequence S.f S.g) :
    (S.map (ι E ⋙ F.mapHomologicalComplex (.up ℤ))).ShortExact :=
  ambientCofiberRawRow_map_shortExact F S.f S.g hS

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

For a commuting map (a,b,c) between two bounded cofiber sequences, if F(a) and F(c) are quasi-isomorphisms then F(b) is a quasi-isomorphism. -/
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

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

In a cofiber sequence X —i→ Y —p→ Z, i is an F-detected weak equivalence if and only if F(Z) is acyclic. -/
theorem ambientCofiber_isWeakEquivalence_iff_quotient_acyclic {X Y Z : Bounded E}
    (i : X ⟶ Y) (p : Y ⟶ Z)
    (hSeq : letI := ambientWaldhausenCategory F; IsCofiberSequence i p) :
    letI := ambientWaldhausenCategory F
    IsWeakEquivalence i ↔ ((F.mapHomologicalComplex (.up ℤ)).obj Z.obj).Acyclic := by
  let _ := ambientWaldhausenCategory F
  exact (ambient_isWeakEquivalence_iff F i).trans
    ((ambientCofiberRawRow_map_shortExact F i p hSeq).quasiIso_f_iff)

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

The bounded ambient Waldhausen structure satisfies the extension axiom for maps of cofiber sequences. -/
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

/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.

For a cofiber sequence X → Y → Q, its cofibration is weak exactly when Q belongs to the canonical class of objects with a weak map from zero. -/
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
/-- Let E be preadditive Quillen exact with a zero object and binary
biproducts, A abelian and F:E → A additive.
On bounded complexes use degreewise admissible monomorphisms as
cofibrations and F-detected quasi-isomorphisms as weak equivalences. Assume F is exact.
Assume F is fully faithful, reflects admissible exactness and has essential
image closed under kernels of epimorphisms between image objects.
For X —i→ Y —p→ Z a cofiber sequence, i is weak exactly when Z
admits all-degree source-cycle conflations and differential factorizations. -/
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

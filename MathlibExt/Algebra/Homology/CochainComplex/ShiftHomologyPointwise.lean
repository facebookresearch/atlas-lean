/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Cycles and homology under cochain shifts

For an integer cochain complex, shift by a places K^{i+a} in degree i
and multiplies its differential by (−1)^a. Existence of homology at i+a
therefore gives homology of the shifted complex at i.

The corresponding cycles and homology isomorphisms preserve the cycle
inclusions and homology quotients. When the boundary kernel or outgoing
cycle quotient exists, the same shift identifies those objects as well.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Homology
also exists for K⟦a⟧ at degree i: multiplying the differential by the unit (−1)ᵃ preserves the
kernels and quotients defining it.
-/
lemma hasHomology_shift (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    (K⟦a⟧).HasHomology i :=
  ShortComplex.hasHomology_of_iso
    ((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).symm

private lemma shiftScIso_hom_tau2 (K : CochainComplex C ℤ) (a i : ℤ) :
    (((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).hom).τ₂ =
      𝟙 (K.X (i + a)) := by
  rfl

private lemma shiftScIso_inv_tau2 (K : CochainComplex C ℤ) (a i : ℤ) :
    (((shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K).inv).τ₂ =
      𝟙 (K.X (i + a)) := by
  rfl

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. There is
a canonical isomorphism e_Z : Zⁱ(K⟦a⟧) ≅ Zⁱ⁺ᵃ(K), induced by the identification of the term
Kⁱ⁺ᵃ and the signed differential.
-/
def shiftCyclesIso (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).cycles i ≅ K.cycles (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.cyclesMapIso e

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. The
signed shift induces a canonical isomorphism e_H : Hⁱ(K⟦a⟧) ≅ Hⁱ⁺ᵃ(K), compatible with the
canonical cycle identification.
-/
def shiftHomologyIso (K : CochainComplex C ℤ) (a i : ℤ) [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).homology i ≅ K.homology (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.homologyMapIso e

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Let e_Z
be the canonical cycles isomorphism and j,j' the cycle inclusions in K⟦a⟧ and K. After
identifying their degree-i terms, e_Z.hom ≫ j' = j.
-/
@[reassoc]
lemma shiftCyclesIso_hom_iCycles (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (shiftCyclesIso K a i).hom ≫ K.iCycles (i + a) = (K⟦a⟧).iCycles i := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  change ShortComplex.cyclesMap e.hom ≫ (K.sc (i + a)).iCycles =
    ((K⟦a⟧).sc i).iCycles
  have he : e.hom.τ₂ = 𝟙 (K.X (i + a)) := shiftScIso_hom_tau2 K a i
  rw [ShortComplex.cyclesMap_i, he]
  change ((K⟦a⟧).sc i).iCycles ≫ 𝟙 ((K⟦a⟧).sc i).X₂ = ((K⟦a⟧).sc i).iCycles
  exact Category.comp_id _

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. For the
canonical cycles isomorphism e_Z : Zⁱ(K⟦a⟧) ≅ Zⁱ⁺ᵃ(K), its inverse satisfies e_Z.inv ≫ j = j',
where j and j' are the respective cycle inclusions.
-/
@[reassoc]
lemma shiftCyclesIso_inv_iCycles (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (shiftCyclesIso K a i).inv ≫ (K⟦a⟧).iCycles i = K.iCycles (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  change ShortComplex.cyclesMap e.inv ≫ ((K⟦a⟧).sc i).iCycles =
    (K.sc (i + a)).iCycles
  have he : e.inv.τ₂ = 𝟙 (K.X (i + a)) := shiftScIso_inv_tau2 K a i
  rw [ShortComplex.cyclesMap_i, he]
  change (K.sc (i + a)).iCycles ≫ 𝟙 (K.sc (i + a)).X₂ = (K.sc (i + a)).iCycles
  exact Category.comp_id _

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Let
e_Z,e_H be the canonical cycles and homology isomorphisms, and let π,π' be the homology
quotients in K⟦a⟧ and K. They form a commutative square: π ≫ e_H.hom = e_Z.hom ≫ π'.
-/
@[reassoc]
lemma shiftHomologyIso_homologyπ (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    (K⟦a⟧).homologyπ i ≫ (shiftHomologyIso K a i).hom =
      (shiftCyclesIso K a i).hom ≫ K.homologyπ (i + a) := by
  letI := hasHomology_shift K a i
  let e : (K⟦a⟧).sc i ≅ K.sc (i + a) :=
    (shiftShortComplexFunctorIso C a i (i + a) (by omega)).app K
  exact ShortComplex.homologyπ_naturality e.hom

/--
Let f : K → L be a morphism of integer cochain complexes in a preadditive category C. Fix a,i
∈ ℤ and assume both K and L have homology at i+a. The shift has terms K^{i+a},L^{i+a} and
differential sign (−1)^a. For the canonical cycles comparisons e_Z(K),e_Z(L), Zⁱ(f⟦a⟧) ≫
e_Z(L).hom = e_Z(K).hom ≫ Zⁱ⁺ᵃ(f).
-/
@[reassoc]
lemma shiftCyclesIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (a i : ℤ)
    [K.HasHomology (i + a)] [L.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    letI := hasHomology_shift L a i
    cyclesMap (f⟦a⟧') i ≫ (shiftCyclesIso L a i).hom =
      (shiftCyclesIso K a i).hom ≫ cyclesMap f (i + a) := by
  letI := hasHomology_shift K a i
  letI := hasHomology_shift L a i
  apply (cancel_mono (L.iCycles (i + a))).1
  simp only [Category.assoc]
  rw [shiftCyclesIso_hom_iCycles, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.cyclesMap_i, CochainComplex.shiftFunctor_map_f']
  simp only [← Category.assoc, shiftCyclesIso_hom_iCycles]

/--
Let f : K → L be a morphism of integer cochain complexes in a preadditive category C. Fix a,i
∈ ℤ and assume both K and L have homology at i+a. The shift has terms K^{i+a},L^{i+a} and
differential sign (−1)^a. For the canonical homology comparisons e_H(K),e_H(L), Hⁱ(f⟦a⟧) ≫
e_H(L).hom = e_H(K).hom ≫ Hⁱ⁺ᵃ(f).
-/
@[reassoc]
lemma shiftHomologyIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) (a i : ℤ)
    [K.HasHomology (i + a)] [L.HasHomology (i + a)] :
    letI := hasHomology_shift K a i
    letI := hasHomology_shift L a i
    homologyMap (f⟦a⟧') i ≫ (shiftHomologyIso L a i).hom =
      (shiftHomologyIso K a i).hom ≫ homologyMap f (i + a) := by
  letI := hasHomology_shift K a i
  letI := hasHomology_shift L a i
  apply (cancel_epi ((K⟦a⟧).homologyπ i)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc, shiftHomologyIso_homologyπ,
    shiftHomologyIso_homologyπ_assoc, HomologicalComplex.homologyπ_naturality]
  exact shiftCyclesIso_naturality_assoc f a i _

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. If the
homology quotient Zⁱ⁺ᵃ(K) → Hⁱ⁺ᵃ(K) has a kernel, then the homology quotient Zⁱ(K⟦a⟧) →
Hⁱ(K⟦a⟧) also has a kernel, transported along the canonical cycles/homology square.
-/
lemma hasKernel_homologyπ_shift (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    HasKernel ((K⟦a⟧).homologyπ i) := by
  letI := hasHomology_shift K a i
  let e : parallelPair ((K⟦a⟧).homologyπ i) 0 ≅ parallelPair (K.homologyπ (i + a)) 0 :=
    parallelPair.ext (shiftCyclesIso K a i) (shiftHomologyIso K a i)
      (shiftHomologyIso_homologyπ K a i) (by simp)
  exact hasLimit_of_iso e.symm

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. If the
cycle inclusion Zⁱ⁺ᵃ(K) → Kⁱ⁺ᵃ has a cokernel, then the shifted cycle inclusion Zⁱ(K⟦a⟧) →
(K⟦a⟧)ⁱ also has a cokernel.
-/
lemma hasCokernel_iCycles_shift (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    HasCokernel ((K⟦a⟧).iCycles i) := by
  letI := hasHomology_shift K a i
  let e : parallelPair ((K⟦a⟧).iCycles i) 0 ≅ parallelPair (K.iCycles (i + a)) 0 :=
    parallelPair.ext (shiftCyclesIso K a i) (Iso.refl _)
      (by
        change (K⟦a⟧).iCycles i ≫ 𝟙 ((K⟦a⟧).X i) =
          (shiftCyclesIso K a i).hom ≫ K.iCycles (i + a)
        exact (Category.comp_id _).trans (shiftCyclesIso_hom_iCycles K a i).symm) (by simp)
  exact hasColimit_of_iso e

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Assume
the homology quotient π' : Zⁱ⁺ᵃ(K) → Hⁱ⁺ᵃ(K) has a kernel. The canonical shift square
identifies ker(π : Zⁱ(K⟦a⟧) → Hⁱ(K⟦a⟧)) with ker π'. These are the boundary kernels at the two
corresponding degrees.
-/
def shiftBoundaryIso (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasKernel_homologyπ_shift K a i
    kernel ((K⟦a⟧).homologyπ i) ≅ kernel (K.homologyπ (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasKernel_homologyπ_shift K a i
  exact kernel.mapIso ((K⟦a⟧).homologyπ i) (K.homologyπ (i + a))
    (shiftCyclesIso K a i) (shiftHomologyIso K a i)
      (shiftHomologyIso_homologyπ K a i)

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Assume
the homology quotient π' : Zⁱ⁺ᵃ(K) → Hⁱ⁺ᵃ(K) has a kernel. Let e_B be the boundary-kernel
comparison, e_Z the cycles comparison, and k,k' the respective kernel inclusions. The square
commutes: e_B.hom ≫ k' = k ≫ e_Z.hom.
-/
@[reassoc]
lemma shiftBoundaryIso_hom_ι (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasKernel (K.homologyπ (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasKernel_homologyπ_shift K a i
    (shiftBoundaryIso K a i).hom ≫ kernel.ι (K.homologyπ (i + a)) =
      kernel.ι ((K⟦a⟧).homologyπ i) ≫ (shiftCyclesIso K a i).hom := by
  letI := hasHomology_shift K a i
  letI := hasKernel_homologyπ_shift K a i
  simp [shiftBoundaryIso, kernel.mapIso]

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Assume
the cycle inclusion j' : Zⁱ⁺ᵃ(K) → Kⁱ⁺ᵃ has a cokernel. The shift identifies the cokernel of j
: Zⁱ(K⟦a⟧) → (K⟦a⟧)ⁱ with the cokernel of j', using the common term Kⁱ⁺ᵃ.
-/
def shiftOutgoingIso (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasCokernel_iCycles_shift K a i
    cokernel ((K⟦a⟧).iCycles i) ≅ cokernel (K.iCycles (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasCokernel_iCycles_shift K a i
  exact cokernel.mapIso ((K⟦a⟧).iCycles i) (K.iCycles (i + a))
    (shiftCyclesIso K a i) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using
        (shiftCyclesIso_hom_iCycles K a i).symm)

/--
Let K be an integer cochain complex in a preadditive category C and let a,i ∈ ℤ. Use the shift
convention (K⟦a⟧)ⁱ = Kⁱ⁺ᵃ and d_{K⟦a⟧}ⁱ = (−1)ᵃ d_Kⁱ⁺ᵃ. Assume K has homology at i+a. Assume
the cycle inclusion j' : Zⁱ⁺ᵃ(K) → Kⁱ⁺ᵃ has a cokernel. For the quotient comparison e_Q and
the cokernel projections q,q', the canonical maps satisfy q ≫ e_Q.hom = q' after identifying
the shifted term with Kⁱ⁺ᵃ.
-/
@[reassoc]
lemma shiftOutgoingIso_π_hom (K : CochainComplex C ℤ) (a i : ℤ)
    [K.HasHomology (i + a)] [HasCokernel (K.iCycles (i + a))] :
    letI := hasHomology_shift K a i
    letI := hasCokernel_iCycles_shift K a i
    cokernel.π ((K⟦a⟧).iCycles i) ≫ (shiftOutgoingIso K a i).hom =
      cokernel.π (K.iCycles (i + a)) := by
  letI := hasHomology_shift K a i
  letI := hasCokernel_iCycles_shift K a i
  simp [shiftOutgoingIso, cokernel.mapIso]

end CochainComplex

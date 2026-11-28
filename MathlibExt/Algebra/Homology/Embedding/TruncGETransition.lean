/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Canonical transitions between good lower cochain truncations

For lo≤hi, the good cochain truncations have a canonical epimorphism
τ≥lo K→τ≥hi K factoring the projection from K. It is natural in K and
induces isomorphisms on homology at all degrees q≥hi.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

set_option autoImplicit false

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)

/--
Let K be an integer cochain complex in an abelian category A, let lo≤hi be integers, and write
τ≥m K for good truncation below m. The canonical transition T:τ≥lo K→τ≥hi K is determined by
π_lo ≫ T = π_hi, where π_m:K→τ≥m K is the good-truncation projection.
-/
def truncGETransition (lo hi : ℤ) (h : lo ≤ hi) : K.truncGE lo ⟶ K.truncGE hi := by
  letI : (K.truncGE hi).IsStrictlyGE lo := (K.truncGE hi).isStrictlyGE_of_ge lo hi h
  exact CochainComplex.truncGEMap (K.πTruncGE hi) lo ≫ inv ((K.truncGE hi).πTruncGE lo)

/--
Let K be an integer cochain complex in an abelian category A, let lo≤hi be integers, and write
τ≥m K for good truncation below m. The transition factors the higher-cutoff projection:
K.πTruncGE lo ≫ K.truncGETransition lo hi = K.πTruncGE hi.
-/
@[reassoc (attr := simp)]
theorem πTruncGE_comp_truncGETransition (lo hi : ℤ) (h : lo ≤ hi) :
    K.πTruncGE lo ≫ K.truncGETransition lo hi h = K.πTruncGE hi := by
  let : (K.truncGE hi).IsStrictlyGE lo := (K.truncGE hi).isStrictlyGE_of_ge lo hi h
  change K.πTruncGE lo ≫
      (CochainComplex.truncGEMap (K.πTruncGE hi) lo ≫ inv ((K.truncGE hi).πTruncGE lo)) =
    K.πTruncGE hi
  rw [← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

private theorem πTruncGE_epi_native (n : ℤ) : Epi (K.πTruncGE n) := by
  change Epi (HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE n))
  infer_instance

/--
Let K be an integer cochain complex in an abelian category A, let lo≤hi be integers, and write
τ≥m K for good truncation below m. The transition T:τ≥lo K→τ≥hi K is an epimorphism, since the
projection π_hi factors through π_lo followed by T.
-/
instance truncGETransition_epi (lo hi : ℤ) (h : lo ≤ hi) :
    Epi (K.truncGETransition lo hi h) := by
  let : Epi (K.πTruncGE hi) := πTruncGE_epi_native K hi
  exact epi_of_epi_fac (K.πTruncGE_comp_truncGETransition lo hi h)

/--
Let K be an integer cochain complex in an abelian category A, let lo≤hi be integers, and write
τ≥m K for good truncation below m. If f:τ≥lo K→τ≥hi K satisfies π_lo ≫ f = π_hi, then f equals
the canonical transition T.
-/
theorem truncGETransition_unique (lo hi : ℤ) (h : lo ≤ hi)
    {f : K.truncGE lo ⟶ K.truncGE hi} (hf : K.πTruncGE lo ≫ f = K.πTruncGE hi) :
    f = K.truncGETransition lo hi h := by
  let : Epi (K.πTruncGE lo) := πTruncGE_epi_native K lo
  exact (cancel_epi (K.πTruncGE lo)).1
    (hf.trans (K.πTruncGE_comp_truncGETransition lo hi h).symm)

/--
Let K be an integer cochain complex in an abelian category A, let lo≤hi be integers, and write
τ≥m K for good truncation below m. For any integer q≥hi, the transition T induces an
isomorphism H^q(τ≥lo K)→H^q(τ≥hi K). Thus it is a quasi-isomorphism at every retained target
degree.
-/
theorem quasiIsoAt_truncGETransition (lo hi q : ℤ) (h : lo ≤ hi) (hq : hi ≤ q) :
    QuasiIsoAt (K.truncGETransition lo hi h) q := by
  let : QuasiIsoAt (K.πTruncGE lo) q := K.quasiIsoAt_πTruncGE lo q (h.trans hq)
  let : QuasiIsoAt (K.πTruncGE lo ≫ K.truncGETransition lo hi h) q := by
    rw [K.πTruncGE_comp_truncGETransition lo hi h]
    exact K.quasiIsoAt_πTruncGE hi q hq
  exact _root_.quasiIsoAt_of_comp_left
    (K.πTruncGE lo) (K.truncGETransition lo hi h) q

/--
Let f:K→L be a morphism of integer cochain complexes in an abelian category A, and let lo≤hi.
The transition square commutes: T_K ≫ τ≥hi(f) = τ≥lo(f) ≫ T_L.
-/
theorem truncGETransition_naturality {L : CochainComplex A ℤ} (f : K ⟶ L)
    (lo hi : ℤ) (h : lo ≤ hi) :
    K.truncGETransition lo hi h ≫ CochainComplex.truncGEMap f hi =
      CochainComplex.truncGEMap f lo ≫ L.truncGETransition lo hi h := by
  let : Epi (K.πTruncGE lo) := πTruncGE_epi_native K lo
  apply (cancel_epi (K.πTruncGE lo)).1
  calc
    K.πTruncGE lo ≫ K.truncGETransition lo hi h ≫ CochainComplex.truncGEMap f hi =
        K.πTruncGE hi ≫ CochainComplex.truncGEMap f hi :=
      K.πTruncGE_comp_truncGETransition_assoc lo hi h _
    _ = f ≫ L.πTruncGE hi := CochainComplex.πTruncGE_naturality f hi
    _ = f ≫ L.πTruncGE lo ≫ L.truncGETransition lo hi h := by
      rw [L.πTruncGE_comp_truncGETransition lo hi h]
    _ = K.πTruncGE lo ≫ CochainComplex.truncGEMap f lo ≫ L.truncGETransition lo hi h :=
      (CochainComplex.πTruncGE_naturality_assoc f lo _).symm

private theorem πTruncGE_f_inv_of_lt (lo hi : ℤ) (h : lo < hi) :
    (K.πTruncGE lo).f hi = (K.truncGEXIso lo hi h).inv := by
  let e := ComplexShape.embeddingUpIntGE lo
  have he : e.f (hi - lo).natAbs = hi := by
    change lo + ((hi - lo).natAbs : ℤ) = hi
    rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel]
  have hb : ¬ e.BoundaryGE (hi - lo).natAbs := by
    change ¬ (ComplexShape.embeddingUpIntGE lo).BoundaryGE (hi - lo).natAbs
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  change (HomologicalComplex.πTruncGE K e).f hi =
    (HomologicalComplex.truncGEXIso K e he hb).inv
  rw [HomologicalComplex.πTruncGE, e.liftExtend_f _ _ he,
    K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e he hb]
  simp only [HomologicalComplex.truncGEXIso, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private theorem πTruncGE_f_at_cutoff (hi : ℤ) :
    (K.πTruncGE hi).f hi = K.pOpcycles hi ≫ (K.truncGEXIsoOpcycles hi).inv := by
  let e := ComplexShape.embeddingUpIntGE hi
  have he : e.f (0 : ℕ) = hi := by
    change hi + 0 = hi
    exact add_zero hi
  have hb : e.BoundaryGE (0 : ℕ) := (ComplexShape.boundaryGE_embeddingUpIntGE_iff hi 0).2 rfl
  change (HomologicalComplex.πTruncGE K e).f hi =
    K.pOpcycles hi ≫ (HomologicalComplex.truncGEXIsoOpcycles K e he hb).inv
  rw [HomologicalComplex.πTruncGE, e.liftExtend_f _ _ he,
    K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e he hb]
  simp only [HomologicalComplex.truncGEXIsoOpcycles, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/--
Let K be an integer cochain complex in an abelian category A and let lo<hi. In degree hi, the
lower truncation identifies with K^hi and the higher truncation with its opcycles quotient.
Under these coordinate isomorphisms, the transition is K.pOpcycles hi:K^hi→opcycles^hi(K).
-/
@[reassoc]
theorem truncGETransition_f_comp_truncGEXIsoOpcycles_hom (lo hi : ℤ) (h : lo < hi) :
    (K.truncGETransition lo hi h.le).f hi ≫ (K.truncGEXIsoOpcycles hi).hom =
      (K.truncGEXIso lo hi h).hom ≫ K.pOpcycles hi := by
  have hf := congrArg (fun f : K ⟶ K.truncGE hi => f.f hi)
    (K.πTruncGE_comp_truncGETransition lo hi h.le)
  change (K.πTruncGE lo).f hi ≫ (K.truncGETransition lo hi h.le).f hi =
    (K.πTruncGE hi).f hi at hf
  rw [πTruncGE_f_inv_of_lt K lo hi h, πTruncGE_f_at_cutoff K hi] at hf
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun f => (K.truncGEXIso lo hi h).hom ≫ f ≫ (K.truncGEXIsoOpcycles hi).hom) hf

/-- In an abelian category C, let K be an integer cochain complex and n an integer.
The transition between the two good truncations of K at the same cutoff n
is the identity of K.truncGE n. -/
@[simp]
theorem truncGETransition_self (n : ℤ) :
    K.truncGETransition n n le_rfl = 𝟙 (K.truncGE n) := by
  exact (K.truncGETransition_unique n n le_rfl
    (f := 𝟙 (K.truncGE n)) (by simp only [Category.comp_id])).symm

end CochainComplex

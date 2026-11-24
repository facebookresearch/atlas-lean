/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Transitions between good lower truncations

A lower cutoff maps to a higher cutoff through the original good truncations.
The map is determined by the two canonical projections. At the higher cutoff,
its actual component is the quotient by the incoming differential.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

set_option autoImplicit false

universe u v

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)

/-- The canonical map from a good lower truncation to one with a higher cutoff. -/
def truncGETransition (lo hi : ℤ) (h : lo ≤ hi) : K.truncGE lo ⟶ K.truncGE hi := by
  letI : (K.truncGE hi).IsStrictlyGE lo := (K.truncGE hi).isStrictlyGE_of_ge lo hi h
  exact CochainComplex.truncGEMap (K.πTruncGE hi) lo ≫ inv ((K.truncGE hi).πTruncGE lo)

/-- The transition factors the canonical projection at the higher cutoff. -/
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

/-- The transition between the original good truncations is an epimorphism. -/
instance truncGETransition_epi (lo hi : ℤ) (h : lo ≤ hi) :
    Epi (K.truncGETransition lo hi h) := by
  let : Epi (K.πTruncGE hi) := πTruncGE_epi_native K hi
  exact epi_of_epi_fac (K.πTruncGE_comp_truncGETransition lo hi h)

/-- The original projection triangle determines the transition uniquely. -/
theorem truncGETransition_unique (lo hi : ℤ) (h : lo ≤ hi)
    {f : K.truncGE lo ⟶ K.truncGE hi} (hf : K.πTruncGE lo ≫ f = K.πTruncGE hi) :
    f = K.truncGETransition lo hi h := by
  let : Epi (K.πTruncGE lo) := πTruncGE_epi_native K lo
  exact (cancel_epi (K.πTruncGE lo)).1
    (hf.trans (K.πTruncGE_comp_truncGETransition lo hi h).symm)

/-- The original lower-cutoff transition preserves homology at and above its target cutoff. -/
theorem quasiIsoAt_truncGETransition (lo hi q : ℤ) (h : lo ≤ hi) (hq : hi ≤ q) :
    QuasiIsoAt (K.truncGETransition lo hi h) q := by
  let : QuasiIsoAt (K.πTruncGE lo) q := K.quasiIsoAt_πTruncGE lo q (h.trans hq)
  let : QuasiIsoAt (K.πTruncGE lo ≫ K.truncGETransition lo hi h) q := by
    rw [K.πTruncGE_comp_truncGETransition lo hi h]
    exact K.quasiIsoAt_πTruncGE hi q hq
  exact _root_.quasiIsoAt_of_comp_left
    (K.πTruncGE lo) (K.truncGETransition lo hi h) q

/-- Changing cutoff commutes with the truncation of the original cochain map. -/
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

/-- At the higher cutoff, the transition is the original projection onto opcycles,
under the native coordinate isomorphisms of both truncations. -/
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

end CochainComplex

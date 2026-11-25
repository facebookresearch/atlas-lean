/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.PartialTotalHomologyCoordinates
public import MathlibExt.Algebra.Homology.PartialTotalStep
public import MathlibExt.Algebra.Homology.PartialTotalSignedRowHomology
public import MathlibExt.Algebra.Homology.ShortComplex.MiddleQuasiIso

/-!
# First-quadrant total quasi-isomorphisms

A morphism of nonnegative bicomplexes which is a quasi-isomorphism on every
outer row induces quasi-isomorphisms on every finite partial total and on the
full direct-sum total complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

private theorem signedRowMap_comp_signedRowIso_hom
    (φ : B ⟶ B') (p : ℕ) :
    signedRowMap φ p ≫ (B'.signedRowIso p).hom =
      (B.signedRowIso p).hom ≫ φ.f p := by
  ext q
  change (φ.f p).f q ≫
      (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 ((B'.X p).X q)) =
    (((ComplexShape.down ℕ).ε p) ^ q • 𝟙 ((B.X p).X q)) ≫
      (φ.f p).f q
  rw [Linear.comp_units_smul, Linear.units_smul_comp,
    Category.comp_id, Category.id_comp]

private theorem quasiIso_signedRowMap_of_objwise
    (φ : B ⟶ B') (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) (p : ℕ) :
    QuasiIso (signedRowMap φ p) := by
  have hcomp : QuasiIso
      (signedRowMap φ p ≫ (B'.signedRowIso p).hom) := by
    rw [signedRowMap_comp_signedRowIso_hom]
    let _ : QuasiIso (φ.f p) := hφ p
    infer_instance
  let _ : QuasiIso
      (signedRowMap φ p ≫ (B'.signedRowIso p).hom) := hcomp
  let _ : QuasiIso (B'.signedRowIso p).hom := inferInstance
  exact quasiIso_of_comp_right
    (signedRowMap φ p) (B'.signedRowIso p).hom

private theorem quasiIso_totalRowMap_of_objwise
    (φ : B ⟶ B') (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) (p : ℕ) :
    QuasiIso (totalRowMap φ p) := by
  change QuasiIso (HomologicalComplex.extendMap (signedRowMap φ p)
    (ComplexShape.embeddingDown'Add 1 p))
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (φ := signedRowMap φ p)
    (e := ComplexShape.embeddingDown'Add 1 p)).2
      (quasiIso_signedRowMap_of_objwise φ hφ p)

/-- A rowwise quasi-isomorphism of first-quadrant bicomplexes induces a
quasi-isomorphism on every finite partial total. -/
theorem quasiIso_partialTotalHom_of_objwise
    (φ : B ⟶ B') (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) (p : ℕ) :
    QuasiIso (B.partialTotalHom φ p) := by
  induction p with
  | zero =>
      let f := partialTotalStepShortComplexMap φ 0
      have h₁ : QuasiIso f.τ₁ := by
        let _ : IsIso f.τ₁ :=
          IsZero.isIso (isZero_zero (ChainComplex C ℕ))
            (isZero_zero (ChainComplex C ℕ)) f.τ₁
        infer_instance
      have h₃ : QuasiIso f.τ₃ := by
        dsimp only [f, partialTotalStepShortComplexMap,
          partialTotalZeroShortComplexMap]
        exact quasiIso_totalRowMap_of_objwise φ hφ 0
      exact HomologicalComplex.HomologySequence.quasiIso_τ₂ f
        B.partialTotalZeroShortExact B'.partialTotalZeroShortExact h₁ h₃
  | succ m ih =>
      let f := B.partialTotalSuccShortComplexMap φ m
      have h₃ : QuasiIso f.τ₃ := by
        dsimp only [f, partialTotalSuccShortComplexMap]
        exact quasiIso_totalRowMap_of_objwise φ hφ (m + 1)
      exact HomologicalComplex.HomologySequence.quasiIso_τ₂ f
        (B.partialTotalSuccShortExact m)
        (B'.partialTotalSuccShortExact m) ih h₃

/-- A rowwise quasi-isomorphism of first-quadrant bicomplexes induces a
quasi-isomorphism on their full direct-sum total complexes. -/
theorem quasiIso_totalMap_of_objwise_firstQuadrant
    (φ : B ⟶ B') (hφ : ∀ p : ℕ, QuasiIso (φ.f p)) :
    QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let s := n + 1
  let f := HomologicalComplex.homologyMap (B.partialTotalHom φ s) n
  let i := HomologicalComplex.homologyMap (B.partialTotalι s) n
  let i' := HomologicalComplex.homologyMap (B'.partialTotalι s) n
  let t := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) n
  let _ : QuasiIso (B.partialTotalHom φ s) :=
    quasiIso_partialTotalHom_of_objwise φ hφ s
  let _ : IsIso f := by
    dsimp only [f]
    infer_instance
  let _ : Epi i := by
    dsimp only [i, s]
    exact B.epi_homologyMap_partialTotalι_of_le (n + 1) n (Nat.le_succ n)
  let _ : Mono i := by
    dsimp only [i, s]
    exact B.mono_homologyMap_partialTotalι_of_lt (n + 1) n (Nat.lt_succ_self n)
  let _ : IsIso i := isIso_of_mono_of_epi _
  let _ : Epi i' := by
    dsimp only [i', s]
    exact B'.epi_homologyMap_partialTotalι_of_le (n + 1) n (Nat.le_succ n)
  let _ : Mono i' := by
    dsimp only [i', s]
    exact B'.mono_homologyMap_partialTotalι_of_lt (n + 1) n (Nat.lt_succ_self n)
  let _ : IsIso i' := isIso_of_mono_of_epi _
  have hnat : f ≫ i' = i ≫ t := by
    dsimp only [f, i, i', t]
    simpa only [HomologicalComplex.homologyMap_comp] using
      congrArg (fun k => HomologicalComplex.homologyMap k n)
        (B.partialTotalHom_ι_naturality φ s)
  let _ : IsIso (i ≫ t) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_left i t

end HomologicalComplex₂

end

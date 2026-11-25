/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalStep
public import MathlibExt.Algebra.Homology.SpectralSequence.IncreasingHomologicalCore
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Mapping-cone homology of partial-total steps

At bidegree (p, q), the increasing homological core uses the pth
filtration-step mapping cone in cochain degree -p - q. Its homology
is identified with homology of the signed row in chain degree p + q.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The cochain degree selected by the increasing homological core at
bidegree `(p,q)` is minus the chain total degree `p+q`. -/
theorem coreE₁IncreasingHomologicalNat_deg_eq (p q : ℕ) :
    (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q) =
      -((p + q : ℕ) : ℤ) := by
  change -(p : ℤ) - (q : ℤ) = -((p + q : ℕ) : ℤ)
  omega

/-- The homology object selected by the increasing core from the mapping
cone of the `p`th filtration step.  This is not yet packaged as a spectral
page. -/
noncomputable abbrev partialTotalStepE₁Homology (p q : ℕ) : C :=
  (CochainComplex.mappingCone
      (B.partialTotalStepCochainShortComplex p).f).homology
    ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
      (p, q))

/-- The third object of the cochain filtration step is the signed row,
extended from chain degree `n` to cochain degree `-n`. -/
noncomputable def partialTotalStepCochainX₃Iso (p : ℕ) :
    (B.partialTotalStepCochainShortComplex p).X₃ ≅
      (B.totalRow p).extend ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    (eqToIso (B.partialTotalStepShortComplex_X₃ p))

/-- The third leg of an extended filtration step, followed by its canonical
row coordinate, is the extension of the row quotient. -/
theorem partialTotalStepCochain_g_comp_X₃Iso_hom_heq (p : ℕ) :
    HEq
      ((B.partialTotalStepCochainShortComplex p).g ≫
        (B.partialTotalStepCochainX₃Iso p).hom)
      (HomologicalComplex.extendMap
        (B.partialTotalRowQuotient p) ComplexShape.embeddingDownNat) := by
  cases p with
  | zero =>
      apply heq_of_eq
      let E := ComplexShape.embeddingDownNat.extendFunctor C
      let R := B.partialTotalStepShortComplex 0
      let hX₃ : R.X₃ = B.totalRow 0 :=
        B.partialTotalStepShortComplex_X₃ 0
      have hh : hX₃ = rfl := Subsingleton.elim _ _
      have hEqToIso :
          (eqToIso hX₃).hom = 𝟙 (B.totalRow 0) := by
        rw [hh]
        rfl
      have hMapIso :
          (E.mapIso (eqToIso hX₃)).hom =
            𝟙 (E.obj (B.totalRow 0)) := by
        change E.map (eqToIso hX₃).hom =
          𝟙 (E.obj (B.totalRow 0))
        rw [hEqToIso]
        exact E.map_id R.X₃
      have hMapG : E.map R.g =
          E.map (B.partialTotalRowQuotient 0) := by
        exact congrArg (fun f => E.map f)
          B.partialTotalStepShortComplex_g_zero
      dsimp only [partialTotalStepCochainShortComplex,
        partialTotalStepCochainX₃Iso]
      change E.map R.g ≫ (E.mapIso (eqToIso hX₃)).hom =
        E.map (B.partialTotalRowQuotient 0)
      rw [hMapG, hMapIso]
      exact Category.comp_id _
  | succ m =>
      apply heq_of_eq
      let E := ComplexShape.embeddingDownNat.extendFunctor C
      let R := B.partialTotalStepShortComplex (m + 1)
      let hX₃ : R.X₃ = B.totalRow (m + 1) :=
        B.partialTotalStepShortComplex_X₃ (m + 1)
      have hh : hX₃ = rfl := Subsingleton.elim _ _
      have hEqToIso :
          (eqToIso hX₃).hom = 𝟙 (B.totalRow (m + 1)) := by
        rw [hh]
        rfl
      have hMapIso :
          (E.mapIso (eqToIso hX₃)).hom =
            𝟙 (E.obj (B.totalRow (m + 1))) := by
        change E.map (eqToIso hX₃).hom =
          𝟙 (E.obj (B.totalRow (m + 1)))
        rw [hEqToIso]
        exact E.map_id R.X₃
      have hMapG : E.map R.g =
          E.map (B.partialTotalRowQuotient (m + 1)) := by
        exact congrArg (fun f => E.map f)
          (B.partialTotalStepShortComplex_g_succ m)
      dsimp only [partialTotalStepCochainShortComplex,
        partialTotalStepCochainX₃Iso]
      change E.map R.g ≫ (E.mapIso (eqToIso hX₃)).hom =
        E.map (B.partialTotalRowQuotient (m + 1))
      rw [hMapG, hMapIso]
      exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- Supported component of the inverse step-row cochain isomorphism. -/
theorem partialTotalStepCochainX₃Iso_inv_f_heq (p n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso p).inv.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow p).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).hom := by
  let e := ComplexShape.embeddingDownNat
  let K := (B.partialTotalStepShortComplex p).X₃
  let T := B.totalRow p
  let hStep : K = T := by
    simpa only [K, T] using B.partialTotalStepShortComplex_X₃ p
  have hK : (K.extend e).X (e.f n) = K.X n := by
    change HomologicalComplex.extend.X K (e.r (e.f n)) = K.X n
    rw [e.r_eq_some rfl]
    rfl
  have hT : (T.extend e).X (e.f n) = T.X n := by
    change HomologicalComplex.extend.X T (e.r (e.f n)) = T.X n
    rw [e.r_eq_some rfl]
    rfl
  let hX : K.X n = T.X n :=
    congr_fun (congr_arg HomologicalComplex.X hStep) n
  have hTHom : (T.extendXIso e rfl).hom = eqToHom hT := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  have hKInv : (K.extendXIso e rfl).inv = eqToHom hK.symm := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  change HEq
    ((HomologicalComplex.extendMap (eqToHom hStep.symm) e).f (e.f n))
    ((T.extendXIso e rfl).hom)
  rw [HomologicalComplex.extendMap_f (φ := eqToHom hStep.symm)
    (e := e) rfl, HomologicalComplex.eqToHom_f, hTHom, hKInv]
  have hConj :
      HEq (eqToHom hT ≫ eqToHom hX.symm ≫ eqToHom hK.symm)
        (eqToHom hX.symm) :=
    (CategoryTheory.conj_eqToHom_iff_heq
      (eqToHom hT ≫ eqToHom hX.symm ≫ eqToHom hK.symm)
      (eqToHom hX.symm) hT hK).mp rfl
  exact hConj.trans
    ((CategoryTheory.eqToHom_heq_id_dom _ _ hX.symm).trans
      (CategoryTheory.eqToHom_heq_id_cod _ _ hT).symm)

set_option backward.isDefEq.respectTransparency false in
/-- Supported component of the forward step-row cochain isomorphism. -/
theorem partialTotalStepCochainX₃Iso_hom_f_heq (p n : ℕ) :
    HEq ((B.partialTotalStepCochainX₃Iso p).hom.f
      (ComplexShape.embeddingDownNat.f n))
      ((B.totalRow p).extendXIso
        ComplexShape.embeddingDownNat (i := n)
          (i' := ComplexShape.embeddingDownNat.f n) rfl).inv := by
  let e := ComplexShape.embeddingDownNat
  let K := (B.partialTotalStepShortComplex p).X₃
  let T := B.totalRow p
  let hStep : K = T := by
    simpa only [K, T] using B.partialTotalStepShortComplex_X₃ p
  have hK : (K.extend e).X (e.f n) = K.X n := by
    change HomologicalComplex.extend.X K (e.r (e.f n)) = K.X n
    rw [e.r_eq_some rfl]
    rfl
  have hT : (T.extend e).X (e.f n) = T.X n := by
    change HomologicalComplex.extend.X T (e.r (e.f n)) = T.X n
    rw [e.r_eq_some rfl]
    rfl
  let hX : K.X n = T.X n :=
    congr_fun (congr_arg HomologicalComplex.X hStep) n
  have hKHom : (K.extendXIso e rfl).hom = eqToHom hK := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  have hTInv : (T.extendXIso e rfl).inv = eqToHom hT.symm := by
    dsimp only [HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    rfl
  change HEq
    ((HomologicalComplex.extendMap (eqToHom hStep) e).f (e.f n))
    ((T.extendXIso e rfl).inv)
  rw [HomologicalComplex.extendMap_f (φ := eqToHom hStep)
    (e := e) rfl, HomologicalComplex.eqToHom_f, hKHom, hTInv]
  have hConj :
      HEq (eqToHom hK ≫ eqToHom hX ≫ eqToHom hT.symm)
        (eqToHom hX) :=
    (CategoryTheory.conj_eqToHom_iff_heq
      (eqToHom hK ≫ eqToHom hX ≫ eqToHom hT.symm)
      (eqToHom hX) hK hT).mp rfl
  exact hConj.trans
    ((CategoryTheory.eqToHom_heq_id_cod _ _ hX).trans
      (CategoryTheory.eqToHom_heq_id_dom _ _ hT.symm).symm)

/-- Mapping-cone homology of the `p`th filtration step in bidegree `(p,q)`
is canonically the homology of the signed `p`th row in total degree `p+q`.

At `p=0` this uses the zero-stage short exact sequence; at `p=m+1` it uses
the successor short exact sequence. -/
noncomputable def partialTotalStepE₁HomologyIso (p q : ℕ) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology (p + q) := by
  let S := B.partialTotalStepCochainShortComplex p
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact p
  let desc := CochainComplex.mappingCone.descShortComplex S
  let _ : QuasiIso desc :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hdeg : ComplexShape.embeddingDownNat.f (p + q) =
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q) := by
    change -((p + q : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
    omega
  exact asIso (HomologicalComplex.homologyMap desc
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q))) ≪≫
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso p)
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q)) ≪≫
    (B.totalRow p).extendHomologyIso ComplexShape.embeddingDownNat hdeg

/-- Mapping-cone homology of the `p`th filtration step in a chosen total
degree `n=p+q`. -/
noncomputable def partialTotalStepE₁HomologyIsoAt
    (p q n : ℕ) (h : p + q = n) :
    B.partialTotalStepE₁Homology p q ≅
      (B.totalRow p).homology n := by
  let S := B.partialTotalStepCochainShortComplex p
  let hS : S.ShortExact := B.partialTotalStepCochainShortExact p
  let desc := CochainComplex.mappingCone.descShortComplex S
  let _ : QuasiIso desc :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hdeg : ComplexShape.embeddingDownNat.f n =
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q) := by
    change -((n : ℕ) : ℤ) = -(p : ℤ) - (q : ℤ)
    omega
  exact asIso (HomologicalComplex.homologyMap desc
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q))) ≪≫
    HomologicalComplex.homologyMapIso (B.partialTotalStepCochainX₃Iso p)
      ((CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).deg
        (p, q)) ≪≫
    (B.totalRow p).extendHomologyIso ComplexShape.embeddingDownNat hdeg

end HomologicalComplex₂

end

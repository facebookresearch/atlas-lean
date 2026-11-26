/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Associativity of cycle and cohomology pairings

Consider nonnegative cochain complexes of abelian groups, with tensor product
over ℤ. Let P_AB:A⊗B → AB, P_BC:B⊗C → BC,
P_L:AB⊗C → D_L and P_R:A⊗BC → D_R be cochain graded pairings,
and let f:D_L → D_R be a cochain map.

At specified degrees p,q,r, assume the two iterated term pairings agree
after applying f on the left, the tensor associator on the right, and
the degree identification (p+q)+r=p+(q+r). Then the corresponding pairings
of cycle objects agree by the same maps and degree identification.
The same associativity equality descends to the cohomology pairings.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace HomologicalComplex.CochainGradedPairing

private theorem cyclesDegreeTransport (K : CochainComplex AddCommGrpCat.{s} ℕ)
    (i j : ℕ) (h : i = j) :
    eqToHom (congrArg (fun n => K.cycles n) h) ≫ K.iCycles j =
      K.iCycles i ≫ eqToHom (congrArg K.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem homologyDegreeTransport (K : CochainComplex AddCommGrpCat.{s} ℕ)
    (i j : ℕ) (h : i = j) :
    K.homologyπ i ≫ eqToHom (congrArg (fun n => K.homology n) h) =
      eqToHom (congrArg (fun n => K.cycles n) h) ≫ K.homologyπ j := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- For nonnegative cochain complexes of abelian groups, let
P_AB:A⊗B → AB, P_BC:B⊗C → BC, P_L:AB⊗C → D_L and
P_R:A⊗BC → D_R be cochain graded pairings, and f:D_L → D_R a
cochain map. Fix p,q,r. If the term pairings satisfy
f(P_L(P_AB(x,y),z))=P_R(x,P_BC(y,z)) as tensor maps, with the tensor
associator and the degree identification (p+q)+r=p+(q+r), then the
same equality holds on Zᵖ(A)⊗Zᑫ(B)⊗Zʳ(C), using the induced cycle
pairings and cycle map of f. -/
theorem pairCycles_assoc
    {A B C AB BC DL DR : CochainComplex AddCommGrpCat.{s} ℕ}
    (PAB : CochainGradedPairing A B AB) (PBC : CochainGradedPairing B C BC)
    (PL : CochainGradedPairing AB C DL) (PR : CochainGradedPairing A BC DR)
    (f : DL ⟶ DR) (p q r : ℕ)
    (h : (PAB.pair p q ⊗ₘ 𝟙 (C.X r)) ≫ PL.pair (p + q) r ≫ f.f ((p + q) + r) ≫
        eqToHom (congrArg DR.X (Nat.add_assoc p q r)) =
      (α_ (A.X p) (B.X q) (C.X r)).hom ≫
        (𝟙 (A.X p) ⊗ₘ PBC.pair q r) ≫ PR.pair p (q + r)) :
    (PAB.pairCycles p q ⊗ₘ 𝟙 (C.cycles r)) ≫ PL.pairCycles (p + q) r ≫
      HomologicalComplex.cyclesMap f ((p + q) + r) ≫
      eqToHom (congrArg (fun n => DR.cycles n) (Nat.add_assoc p q r)) =
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (𝟙 (A.cycles p) ⊗ₘ PBC.pairCycles q r) ≫ PR.pairCycles p (q + r) := by
  apply (cancel_mono (DR.iCycles (p + (q + r)))).1
  have hl : ((PAB.pairCycles p q ⊗ₘ 𝟙 (C.cycles r)) ≫ PL.pairCycles (p + q) r ≫
      HomologicalComplex.cyclesMap f ((p + q) + r) ≫
      eqToHom (congrArg (fun n => DR.cycles n) (Nat.add_assoc p q r))) ≫
      DR.iCycles (p + (q + r)) =
      (((A.iCycles p ⊗ₘ B.iCycles q) ≫ PAB.pair p q) ⊗ₘ C.iCycles r) ≫
        PL.pair (p + q) r ≫ f.f ((p + q) + r) ≫ eqToHom (congrArg DR.X (Nat.add_assoc p q r)) := by
    simp only [Category.assoc]
    rw [cyclesDegreeTransport DR ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)]
    rw
        [← Category.assoc (HomologicalComplex.cyclesMap f ((p + q) + r)),
          HomologicalComplex.cyclesMap_i]
    simp only [Category.assoc, pairCycles_i_assoc]
    rw [← Category.assoc (PAB.pairCycles p q ⊗ₘ 𝟙 (C.cycles r)), tensorHom_comp_tensorHom,
      pairCycles_i, Category.id_comp]
  have hr : ((α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
      (𝟙 (A.cycles p) ⊗ₘ PBC.pairCycles q r) ≫ PR.pairCycles p (q + r)) ≫
      DR.iCycles (p + (q + r)) =
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (A.iCycles p ⊗ₘ ((B.iCycles q ⊗ₘ C.iCycles r) ≫ PBC.pair q r)) ≫
        PR.pair p (q + r) := by
    simp only [Category.assoc]
    rw [pairCycles_i]
    rw [← Category.assoc (𝟙 (A.cycles p) ⊗ₘ PBC.pairCycles q r), tensorHom_comp_tensorHom,
      pairCycles_i, Category.id_comp]
  have htL : (((A.iCycles p ⊗ₘ B.iCycles q) ≫ PAB.pair p q) ⊗ₘ C.iCycles r) =
      ((A.iCycles p ⊗ₘ B.iCycles q) ⊗ₘ C.iCycles r) ≫ (PAB.pair p q ⊗ₘ 𝟙 (C.X r)) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  have htR : (A.iCycles p ⊗ₘ ((B.iCycles q ⊗ₘ C.iCycles r) ≫ PBC.pair q r)) =
      (A.iCycles p ⊗ₘ (B.iCycles q ⊗ₘ C.iCycles r)) ≫ (𝟙 (A.X p) ⊗ₘ PBC.pair q r) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
  rw [hl, hr, htL, htR]
  simp only [Category.assoc]
  rw [h]
  have hn := associator_naturality (A.iCycles p) (B.iCycles q) (C.iCycles r)
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ (𝟙 (A.X p) ⊗ₘ PBC.pair q r) ≫ PR.pair p (q + r)) hn


private theorem tensorEpi {A A' B B' : AddCommGrpCat.{s}}
    (f : A ⟶ A') (g : B ⟶ B') [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  apply (AddCommGrpCat.epi_iff_surjective (f ⊗ₘ g)).mpr
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      obtain ⟨a', ha⟩ := (AddCommGrpCat.epi_iff_surjective f).mp (inferInstance : Epi f) a
      obtain ⟨b', hb⟩ := (AddCommGrpCat.epi_iff_surjective g).mp (inferInstance : Epi g) b
      refine ⟨a' ⊗ₜ[ℤ] b', ?_⟩
      exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b) ha hb
  | add a b ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', ((f ⊗ₘ g).hom.map_add a' b').trans (congrArg₂ (· + ·) ha hb)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- For nonnegative cochain complexes of abelian groups, let
P_AB:A⊗B → AB, P_BC:B⊗C → BC, P_L:AB⊗C → D_L and
P_R:A⊗BC → D_R be cochain graded pairings, and f:D_L → D_R a
cochain map. Fix p,q,r and assume their iterated term pairings agree
as tensor maps after f, the tensor associator and
(p+q)+r=p+(q+r). The induced pairings on
Hᵖ(A)⊗Hᑫ(B)⊗Hʳ(C) then satisfy the same associativity equality,
with H(f) and the same total-degree identification. -/
theorem pairHomology_assoc
    {A B C AB BC DL DR : CochainComplex AddCommGrpCat.{s} ℕ}
    (PAB : CochainGradedPairing A B AB) (PBC : CochainGradedPairing B C BC)
    (PL : CochainGradedPairing AB C DL) (PR : CochainGradedPairing A BC DR)
    (f : DL ⟶ DR) (p q r : ℕ)
    (h : (PAB.pair p q ⊗ₘ 𝟙 (C.X r)) ≫ PL.pair (p + q) r ≫ f.f ((p + q) + r) ≫
        eqToHom (congrArg DR.X (Nat.add_assoc p q r)) =
      (α_ (A.X p) (B.X q) (C.X r)).hom ≫
        (𝟙 (A.X p) ⊗ₘ PBC.pair q r) ≫ PR.pair p (q + r)) :
    (PAB.pairHomology p q ⊗ₘ 𝟙 (C.homology r)) ≫ PL.pairHomology (p + q) r ≫
      HomologicalComplex.homologyMap f ((p + q) + r) ≫
      eqToHom (congrArg (fun n => DR.homology n) (Nat.add_assoc p q r)) =
      (α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
        (𝟙 (A.homology p) ⊗ₘ PBC.pairHomology q r) ≫ PR.pairHomology p (q + r) := by
  let a := A.homologyπ p
  let b := B.homologyπ q
  let c := C.homologyπ r
  let e := (a ⊗ₘ b) ⊗ₘ c
  have ha : Epi a := inferInstance
  have hb : Epi b := inferInstance
  have hc : Epi c := inferInstance
  let : Epi (a ⊗ₘ b) := tensorEpi a b
  let : Epi e := tensorEpi (a ⊗ₘ b) c
  apply (cancel_epi e).1
  have hcycles := pairCycles_assoc PAB PBC PL PR f p q r h
  have hl : e ≫ (PAB.pairHomology p q ⊗ₘ 𝟙 (C.homology r)) =
      (PAB.pairCycles p q ⊗ₘ 𝟙 (C.cycles r)) ≫
        (AB.homologyπ (p + q) ⊗ₘ c) := by
    dsimp only [e, a, b]
    rw [tensorHom_comp_tensorHom, tensor_homologyπ_comp_pairHomology, Category.comp_id,
      tensorHom_comp_tensorHom, Category.id_comp]
  have hr : (a ⊗ₘ (b ⊗ₘ c)) ≫ (𝟙 (A.homology p) ⊗ₘ PBC.pairHomology q r) =
      (𝟙 (A.cycles p) ⊗ₘ PBC.pairCycles q r) ≫
        (a ⊗ₘ BC.homologyπ (q + r)) := by
    dsimp only [a, b, c]
    rw [tensorHom_comp_tensorHom, tensor_homologyπ_comp_pairHomology, Category.comp_id,
      tensorHom_comp_tensorHom, Category.id_comp]
  have hpL : (AB.homologyπ (p + q) ⊗ₘ c) ≫ PL.pairHomology (p + q) r =
      PL.pairCycles (p + q) r ≫ DL.homologyπ ((p + q) + r) :=
    tensor_homologyπ_comp_pairHomology PL (p + q) r
  have hpR : (a ⊗ₘ BC.homologyπ (q + r)) ≫ PR.pairHomology p (q + r) =
      PR.pairCycles p (q + r) ≫ DR.homologyπ (p + (q + r)) :=
    tensor_homologyπ_comp_pairHomology PR p (q + r)
  have hL : e ≫ ((PAB.pairHomology p q ⊗ₘ 𝟙 (C.homology r)) ≫ PL.pairHomology (p + q) r ≫
      HomologicalComplex.homologyMap f ((p + q) + r) ≫
      eqToHom (congrArg (fun n => DR.homology n) (Nat.add_assoc p q r))) =
      (PAB.pairCycles p q ⊗ₘ 𝟙 (C.cycles r)) ≫ PL.pairCycles (p + q) r ≫
        HomologicalComplex.cyclesMap f ((p + q) + r) ≫
        eqToHom (congrArg (fun n => DR.cycles n) (Nat.add_assoc p q r)) ≫
        DR.homologyπ (p + (q + r)) := by
    rw [← Category.assoc e, hl]
    simp only [Category.assoc]
    rw [← Category.assoc (AB.homologyπ (p + q) ⊗ₘ c), hpL]
    simp only [Category.assoc]
    rw [← Category.assoc (DL.homologyπ ((p + q) + r)),
      HomologicalComplex.homologyπ_naturality f ((p + q) + r)]
    simp only [Category.assoc]
    rw [homologyDegreeTransport DR ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)]
  have hR : e ≫ ((α_ (A.homology p) (B.homology q) (C.homology r)).hom ≫
      (𝟙 (A.homology p) ⊗ₘ PBC.pairHomology q r) ≫ PR.pairHomology p (q + r)) =
      (α_ (A.cycles p) (B.cycles q) (C.cycles r)).hom ≫
        (𝟙 (A.cycles p) ⊗ₘ PBC.pairCycles q r) ≫ PR.pairCycles p (q + r) ≫
        DR.homologyπ (p + (q + r)) := by
    dsimp only [e]
    rw [← Category.assoc, associator_naturality]
    simp only [Category.assoc]
    rw [← Category.assoc (a ⊗ₘ (b ⊗ₘ c)), hr]
    simp only [Category.assoc]
    rw [hpR]
  rw [hL, hR]
  exact congrArg (fun k => k ≫ DR.homologyπ (p + (q + r))) hcycles

end HomologicalComplex.CochainGradedPairing

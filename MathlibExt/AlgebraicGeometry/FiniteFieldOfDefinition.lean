/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_exists_intermediateField_finiteDimensional_
comp_pullback_map_eq_of_isAlgebraic.lean`
and
`P2M/Sol/S_AlgebraicGeometry_exists_intermediateField_finiteDimensional_
comp_pullback_map_eq_of_isAlgebraic.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IntermediateField.Basic

@[expose] public section

universe u

open scoped IntermediateField

namespace FinSubfield

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private abbrev FinIF (k K : Type u) [Field k] [Field K] [Algebra k K] :=
  {L : IntermediateField k K // FiniteDimensional k L}

private scoped instance (L : FinIF k K) : FiniteDimensional k L.1 := L.2

private noncomputable def adj [Algebra.IsAlgebraic k K] (x : K) : FinIF k K :=
  ⟨k⟮x⟯, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

private theorem mem_adj [Algebra.IsAlgebraic k K] (x : K) : x ∈ (adj (k := k) x).1 :=
  IntermediateField.mem_adjoin_simple_self k x

private noncomputable def sup2 (L L' : FinIF k K) : FinIF k K :=
  ⟨L.1 ⊔ L'.1, IntermediateField.finiteDimensional_sup L.1 L'.1⟩

private theorem existsUnique_ringHom_forall_comp_eq [Algebra.IsAlgebraic k K]
    (R : Type u) [CommRing R] (φ : ∀ L : FinIF k K, L.1 →+* R)
    (hφ : ∀ (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x : L.1), φ L' ⟨x.1, h x.2⟩ = φ L x) :
    ∃! ψ : K →+* R, ∀ (L : FinIF k K) (x : L.1), ψ x.1 = φ L x := by
  classical
  have hwd : ∀ (L L' : FinIF k K) (x : K) (hx : x ∈ L.1) (hx' : x ∈ L'.1), φ L ⟨x, hx⟩ = φ L'
      ⟨x, hx'⟩ := by
    intro L L' x hx hx'
    rw [← hφ L (sup2 L L') le_sup_left ⟨x, hx⟩, ← hφ L' (sup2 L L') le_sup_right ⟨x, hx'⟩]
  let ψf : K → R := fun x => φ (adj x) ⟨x, mem_adj x⟩
  have hψf : ∀ (L : FinIF k K) (x : K) (hx : x ∈ L.1), ψf x = φ L ⟨x, hx⟩ := fun L x hx => hwd _
      _ _ _ _
  let ψ : K →+* R :=
    { toFun := ψf
      map_one' := by rw [hψf ⟨⊥, inferInstance⟩ 1 (one_mem _)]; exact map_one _
      map_zero' := by rw [hψf ⟨⊥, inferInstance⟩ 0 (zero_mem _)]; exact map_zero _
      map_mul' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x * y) (mul_mem hx hy), ← map_mul]
        rfl
      map_add' := by
        intro x y
        let L := sup2 (adj (k := k) x) (adj y)
        have hx : x ∈ L.1 := (le_sup_left : (adj (k := k) x).1 ≤ L.1) (mem_adj x)
        have hy : y ∈ L.1 := (le_sup_right : (adj (k := k) y).1 ≤ L.1) (mem_adj y)
        rw [hψf L x hx, hψf L y hy, hψf L (x + y) (add_mem hx hy), ← map_add]
        rfl }
  refine ⟨ψ, fun L x => hψf L x.1 x.2, ?_⟩
  intro ψ' hψ'
  ext x
  change ψ' x = ψf x
  rw [hψf (adj x) x (mem_adj x)]
  exact hψ' (adj x) ⟨x, mem_adj x⟩

end FinSubfield

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace FinSubfieldAux

variable (k K : Type u) [Field k] [Field K] [Algebra k K] (X : Scheme.{u}) (fX : X ⟶ Spec
    (CommRingCat.of k))

private abbrev FinIF := FinSubfield.FinIF k K


private noncomputable abbrev gF (L : FinIF k K) : Spec (CommRingCat.of L.1) ⟶ Spec
    (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L.1))

private noncomputable abbrev gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

private theorem incl_comp_gF {L₂ L₁ : FinIF k K} (h : L₂.1 ≤ L₁.1) :
    Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) ≫ gF k K L₂ = gF k K
        L₁ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

private theorem toK_comp_gF (L : FinIF k K) :
    Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) ≫ gF k K L = gK k K := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

private noncomputable def D : (FinIF k K)ᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback fX (gF k K i.unop)
  map {i j} f := pullback.map fX (gF k K i.unop) fX (gF k K j.unop) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, incl_comp_gF])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp]
      convert Category.comp_id _
      rw [← Spec.map_id]
      rfl
  map_comp {i j l} f g := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl

private noncomputable def t : D k K X fX ⟶ (Functor.const _).obj (Spec (CommRingCat.of k)) where
  app i := pullback.fst fX (gF k K i.unop) ≫ fX
  naturality {i j} f := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, D]
    rw [← Category.assoc, pullback.lift_fst, Category.comp_id]

private noncomputable def c : Cone (D k K X fX) where
  pt := pullback fX (gK k K)
  π :=
    { app := fun i => pullback.map fX (gK k K) fX (gF k K i.unop) (𝟙 X)
          (Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, toK_comp_gF])
      naturality := by
        intro i j f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, D]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
        · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl }

private scoped instance : IsDirectedOrder (FinIF k K) :=
  ⟨fun L L' => ⟨FinSubfield.sup2 L L', le_sup_left (a := L.1), le_sup_right (a := L.1)⟩⟩

private scoped instance : Nonempty (FinIF k K) := ⟨⟨⊥, inferInstance⟩⟩

private scoped instance : IsFiltered (FinIF k K) := inferInstance

private scoped instance : IsCofiltered (FinIF k K)ᵒᵖ := inferInstance

section RingOf

private noncomputable def ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : B ⟶
    Γ(W, ⊤) :=
  (Scheme.ΓSpecIso B).inv ≫ g.appTop

private noncomputable def toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : W ⟶
    Spec B :=
  ΓSpec.adjunction.homEquiv W (op B) φ.op

private theorem ringOf_toSpec {W : Scheme.{u}} {B : CommRingCat.{u}} (φ : B ⟶ Γ(W, ⊤)) : ringOf
    (toSpec
    φ) = φ :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ

private theorem ext_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} {g₁ g₂ : W ⟶ Spec B} (h :
    ringOf g₁ =
    ringOf g₂) : g₁ = g₂ := by
  apply ext_of_isAffine
  simpa [ringOf, Iso.cancel_iso_inv_left] using h

private theorem toSpec_ringOf {W : Scheme.{u}} {B : CommRingCat.{u}} (g : W ⟶ Spec B) : toSpec
    (ringOf
    g) = g :=
  ext_ringOf (ringOf_toSpec _)

private theorem ringOf_comp_specMap {W : Scheme.{u}} {B B' : CommRingCat.{u}} (g : W ⟶ Spec B)
    (u : B' ⟶
    B) :
    ringOf (g ≫ Spec.map u) = u ≫ ringOf g := by
  simp only [ringOf, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

private theorem ringOf_precomp {W W' : Scheme.{u}} {B : CommRingCat.{u}} (m : W' ⟶ W) (g : W ⟶
    Spec B) :
    ringOf (m ≫ g) = ringOf g ≫ m.appTop := by
  simp only [ringOf, Scheme.Hom.comp_appTop, Category.assoc]

end RingOf

section Limit

variable {k K X fX}

private noncomputable def bot' : FinIF k K := ⟨⊥, inferInstance⟩

private noncomputable def conePhi (s : Cone (D k K X fX)) (L : FinIF k K) : L.1 →+* Γ(s.pt, ⊤) :=
  (ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L))).hom

private theorem ringOf_π_snd (s : Cone (D k K X fX)) (L : FinIF k K) :
    ringOf (s.π.app (op L) ≫ pullback.snd fX (gF k K L)) = CommRingCat.ofHom (conePhi s L) := rfl

private theorem D_obj (i : (FinIF k K)ᵒᵖ) : (D k K X fX).obj i = pullback fX (gF k K i.unop) := rfl

private theorem D_map_fst {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.fst fX (gF k K j.unop) = pullback.fst fX (gF k K i.unop) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem D_map_snd {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) :
    (D k K X fX).map f ≫ pullback.snd fX (gF k K j.unop) =
      pullback.snd fX (gF k K i.unop) ≫ Spec.map (CommRingCat.ofHom (IntermediateField.inclusion
          (leOfHom f.unop)).toRingHom) :=
  pullback.lift_snd _ _ _

private theorem c_π_fst (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.fst fX (gF k K i.unop) = pullback.fst fX (gK k K) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem c_π_snd (i : (FinIF k K)ᵒᵖ) :
    (c k K X fX).π.app i ≫ pullback.snd fX (gF k K i.unop) =
      pullback.snd fX (gK k K) ≫ Spec.map (CommRingCat.ofHom (algebraMap (i.unop).1 K)) :=
  pullback.lift_snd _ _ _

private theorem π_snd_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
      (s.π.app (op L') ≫ pullback.snd fX (gF k K L')) ≫
        Spec.map (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom) := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.snd fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_snd] at this
  erw [Category.assoc]
  exact this.symm

private theorem π_fst_eq (s : Cone (D k K X fX)) {L L' : FinIF k K} (h : L.1 ≤ L'.1) :
    s.π.app (op L) ≫ pullback.fst fX (gF k K L) = s.π.app (op L') ≫ pullback.fst fX (gF k K L')
        := by
  have hw := s.w (homOfLE (show L ≤ L' from h)).op
  have := congrArg (· ≫ pullback.fst fX (gF k K L)) hw
  beta_reduce at this
  erw [Category.assoc, D_map_fst] at this
  exact this.symm

private theorem conePhi_compat (s : Cone (D k K X fX)) (L L' : FinIF k K) (h : L.1 ≤ L'.1) (x :
    L.1) :
    conePhi s L' ⟨x.1, h x.2⟩ = conePhi s L x := by
  have h2 := (congrArg ringOf (π_snd_eq s h)).trans
    (ringOf_comp_specMap (s.π.app (op L') ≫ pullback.snd fX (gF k K L'))
      (CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom))
  change CommRingCat.ofHom (conePhi s L) = _ ≫ CommRingCat.ofHom (conePhi s L') at h2
  have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
  exact h3.symm

variable [Algebra.IsAlgebraic k K]

private noncomputable def conePsi (s : Cone (D k K X fX)) : K →+* Γ(s.pt, ⊤) :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat
      s)).exists.choose

private theorem conePsi_spec (s : Cone (D k K X fX)) (L : FinIF k K) (x : L.1) : conePsi s x.1 =
    conePhi
    s L x :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat
      s)).exists.choose_spec L x

private theorem conePsi_unique (s : Cone (D k K X fX)) (ψ' : K →+* Γ(s.pt, ⊤))
    (h : ∀ (L : FinIF k K) (x : L.1), ψ' x.1 = conePhi s L x) : ψ' = conePsi s :=
  (FinSubfield.existsUnique_ringHom_forall_comp_eq Γ(s.pt, ⊤) (conePhi s) (conePhi_compat
      s)).unique h
    (conePsi_spec s)

private noncomputable def toSpecK (s : Cone (D k K X fX)) : s.pt ⟶ Spec (CommRingCat.of K) :=
  toSpec (CommRingCat.ofHom (conePsi s))

private theorem toSpecK_comp (s : Cone (D k K X fX)) (L : FinIF k K) :
    toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) = s.π.app (op L) ≫ pullback.snd
        fX (gF k K L) := by
  apply ext_ringOf
  refine (ringOf_comp_specMap _ _).trans ?_
  rw [toSpecK, ringOf_toSpec]
  change _ = CommRingCat.ofHom (conePhi s L)
  rw [← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact conePsi_spec s L x

set_option backward.isDefEq.respectTransparency false in
private theorem lift_w (s : Cone (D k K X fX)) :
    (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) ≫ fX = toSpecK s ≫ gK k K := by
  have e1 := congrArg (s.π.app (op bot') ≫ ·) (pullback.condition (f := fX) (g := gF k K bot'))
  have e2 := congrArg (· ≫ gF k K bot') (toSpecK_comp s bot')
  have e3 : (toSpecK s ≫ Spec.map (CommRingCat.ofHom (algebraMap (↥bot'.1) K))) ≫ gF k K bot' =
      toSpecK s ≫ gK k K := by
    erw [Category.assoc, toK_comp_gF]
    try rfl
  beta_reduce at e1 e2
  exact ((Category.assoc _ _ _).trans e1).trans (((Category.assoc _ _ _).symm.trans
      e2.symm).trans e3)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def isLimitCone : IsLimit (c k K X fX) where
  lift s := pullback.lift (s.π.app (op bot') ≫ pullback.fst fX (gF k K bot')) (toSpecK s) (lift_w s)
  fac s j := by
    obtain ⟨L⟩ := j
    apply pullback.hom_ext
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id, pullback.lift_fst]
      exact π_fst_eq s (show bot'.1 ≤ L.1 from bot_le)
    · dsimp only [c, D, Opposite.unop_op]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd]
      exact toSpecK_comp s L
  uniq s m hm := by
    apply pullback.hom_ext
    · have := hm (op bot')
      dsimp only [c, D] at this ⊢
      rw [pullback.lift_fst, ← this, Category.assoc, pullback.lift_fst, Category.comp_id]
    · dsimp only [c, D] at hm ⊢
      rw [pullback.lift_snd]
      apply ext_ringOf
      rw [toSpecK, ringOf_toSpec]
      have key : (ringOf (m ≫ pullback.snd fX (gK k K))).hom = conePsi s := by
        apply conePsi_unique
        intro L x
        have hL := hm (op L)
        dsimp only [Opposite.unop_op] at hL
        have a1 := congrArg (· ≫ pullback.snd fX (gF k K L)) hL
        have a3 := c_π_snd (k := k) (K := K) (X := X) (fX := fX) (op L)
        dsimp only [c, D, Opposite.unop_op] at a1 a3
        have h1 : s.π.app (op L) ≫ pullback.snd fX (gF k K L) =
            (m ≫ pullback.snd fX (gK k K)) ≫ Spec.map (CommRingCat.ofHom (algebraMap L.1 K)) :=
          a1.symm.trans ((Category.assoc _ _ _).trans (((congrArg (m ≫ ·) a3)).trans
              (Category.assoc _ _ _).symm))
        have h2 := (congrArg ringOf h1).trans (ringOf_comp_specMap _ _)
        change CommRingCat.ofHom (conePhi s L) = _ at h2
        have h3 := congrArg (fun φ : CommRingCat.of L.1 ⟶ Γ(s.pt, ⊤) => φ.hom x) h2
        simpa using h3.symm
      have : ringOf (m ≫ pullback.snd fX (gK k K)) = CommRingCat.ofHom (conePsi s) := by
        ext1; exact key
      exact this

end Limit

section Instances

private scoped instance isAffineHom_D_map {i j : (FinIF k K)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((D k K X
    fX).map f) := by
  dsimp only [D]
  haveI : MorphismProperty.IsStableUnderComposition @IsAffineHom :=
    ⟨fun f g hf hg => by haveI := hf; haveI := hg; infer_instance⟩
  exact MorphismProperty.pullbackMap (P := @IsAffineHom)
    (f := fX) (g := gF k K i.unop) (f' := fX) (g' := gF k K j.unop) (i₁ := 𝟙 X)
    (i₂ := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom))
    inferInstance inferInstance (Category.id_comp _).symm (incl_comp_gF k K _).symm

private scoped instance compactSpace_pullback_gF [CompactSpace X] (L : FinIF k K) : CompactSpace
    ↥(pullback fX (gF k K L)) := by
  haveI : IsAffineHom (gF k K L) := inferInstance
  haveI : QuasiCompact (gF k K L) := inferInstance
  infer_instance

private scoped instance quasiSeparatedSpace_pullback_gF [QuasiSeparatedSpace X] (L : FinIF k K) :
    QuasiSeparatedSpace ↥(pullback fX (gF k K L)) := by
  haveI : QuasiSeparated (pullback.fst fX (gF k K L)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K L))

private scoped instance quasiSeparatedSpace_D_obj [QuasiSeparatedSpace X] (i : (FinIF k K)ᵒᵖ) :
    QuasiSeparatedSpace ((D k K X fX).obj i) := by
  dsimp only [D]
  haveI : QuasiSeparated (pullback.fst fX (gF k K i.unop)) := inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst fX (gF k K i.unop))

end Instances

end FinSubfieldAux

namespace AlgebraicGeometry

open FinSubfieldAux in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism between schemes pulled back along an algebraic field
extension descends to a finite intermediate field of definition. -/
public theorem exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [LocallyOfFiniteType fY]
    (f : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ pullback fY (Spec.map
        (CommRingCat.ofHom (algebraMap k K))))
    (hf : f ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∃ (L : IntermediateField k K) (_ : FiniteDimensional k L)
      (g : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ pullback fY (Spec.map
          (CommRingCat.ofHom (algebraMap k L))))

      (hι : Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap k L)) =
        Spec.map (CommRingCat.ofHom (algebraMap k K))),

      g ≫ pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap k L))) =
        pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧

      f ≫ pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map
          (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 Y) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) =
        pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fX (Spec.map
            (CommRingCat.ofHom (algebraMap k L)))
            (𝟙 X) (Spec.map (CommRingCat.ofHom (algebraMap L K))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hι]) ≫ g := by
  classical
  let Dg := FinSubfieldAux.D k K X fX
  let tg := FinSubfieldAux.t k K X fX
  let cg := FinSubfieldAux.c k K X fX
  have hc : IsLimit cg := FinSubfieldAux.isLimitCone
  haveI : LocallyOfFinitePresentation fY :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let a : cg.pt ⟶ Y := f ≫ pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have ha : cg.π ≫ tg = (Functor.const _).map (a ≫ fY) := by
    ext i
    change cg.π.app i ≫ (pullback.fst fX (gF k K i.unop) ≫ fX) = a ≫ fY
    have e1 := FinSubfieldAux.c_π_fst (k := k) (K := K) (X := X) (fX := fX) i
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fX) e1).trans (pullback.condition.trans
      ((congrArg (· ≫ gK k K) hf).symm.trans ((Category.assoc f _ _).trans
        ((congrArg (f ≫ ·) pullback.condition.symm).trans (Category.assoc _ _ _).symm)))))
  haveI hC : ∀ i : (FinSubfieldAux.FinIF k K)ᵒᵖ, CompactSpace ↥(Dg.obj i) :=
    fun i => FinSubfieldAux.compactSpace_pullback_gF k K X fX i.unop
  haveI hQ : ∀ i : (FinSubfieldAux.FinIF k K)ᵒᵖ, QuasiSeparatedSpace ↥(Dg.obj i) :=
    fun i => FinSubfieldAux.quasiSeparatedSpace_pullback_gF k K X fX i.unop
  obtain ⟨i, g₀, hg₀a, hg₀f⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation Dg tg fY cg hc a ha
  obtain ⟨L⟩ := i

  have hw : g₀ ≫ fY = pullback.snd fX (gF k K L) ≫ gF k K L := by
    rw [hg₀f]
    exact pullback.condition
  let g : pullback fX (gF k K L) ⟶ pullback fY (gF k K L) := pullback.lift g₀ (pullback.snd fX
      (gF k K L)) hw
  refine ⟨L.1, L.2, g, toK_comp_gF k K L, pullback.lift_snd _ _ _, ?_⟩
  have hπ : cg.π.app (op L) ≫ g₀ = a := hg₀a
  dsimp only [cg, FinSubfieldAux.c] at hπ
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst]
    exact hπ.symm
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
      hf, pullback.lift_snd]

end AlgebraicGeometry

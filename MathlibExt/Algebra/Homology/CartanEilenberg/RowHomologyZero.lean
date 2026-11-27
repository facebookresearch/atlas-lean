/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.CartanEilenberg.Bicomplex
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowSplittings
public import MathlibExt.Algebra.Homology.ShortComplex.SplittingComp
public import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Original-degree-zero row homology

Let P be Cartan–Eilenberg data for a nonnegative complex L in an abelian category. In resolution
degree a, the chosen split horseshoes give the quotient (p_C ∘ r_T,p_T) : PT₀,ₐ → PH₀,ₐ ⊕ PB₀,ₐ.
It is a cokernel of the actual original-degree incoming differential.

The original-degree-zero homology of the row is therefore H₀(P.bicomplex.Xₐ) ≅ PH₀,ₐ ⊕ PB₀,ₐ.
The opcycles and homology quotient coordinates use this same explicit projection.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.CartanEilenbergResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The map rₐ kills the composite PB₁,ₐ → PC₀,ₐ → PT₀,ₐ of the two stored left
inclusions, and defines its selected cokernel cofork. -/
noncomputable def rowHomologyZeroCompositeCofork (a : ℕ) :
    CokernelCofork
      ((P.cyclesComponentShortComplex a 0).f ≫
        (P.termComponentShortComplex a 0).f) :=
  ShortComplex.Splitting.compLeftCokernelCofork
    (f₁ := (P.cyclesComponentShortComplex a 0).f)
    (g₁ := (P.cyclesComponentShortComplex a 0).g)
    (w₁ := (P.cyclesComponentShortComplex a 0).zero)
    (P.termComponentSplitting a 0)

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. This map is the stored explicit projection from the zero-original-degree
term-resolution component to the homology/boundary biproduct. -/
noncomputable def rowHomologyZeroProjection (a : ℕ) :
    (P.termResolution 0).complex.X a ⟶
      (P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a :=
  (P.rowHomologyZeroCompositeCofork a).π

@[simp]
theorem rowHomologyZeroProjection_eq (a : ℕ) :
    P.rowHomologyZeroProjection a =
      biprod.lift
        ((P.termComponentSplitting a 0).r ≫
          (P.cyclesComponentShortComplex a 0).g)
        (P.termComponentShortComplex a 0).g :=
  rfl

private theorem rowHomologyZeroProjection_comp_fst (a : ℕ) :
    P.rowHomologyZeroProjection a ≫ biprod.fst =
      (P.termComponentSplitting a 0).r ≫
        (P.cyclesComponentShortComplex a 0).g := by
  rw [P.rowHomologyZeroProjection_eq a]
  simp

private theorem rowHomologyZeroProjection_comp_snd (a : ℕ) :
    P.rowHomologyZeroProjection a ≫ biprod.snd =
      (P.termComponentShortComplex a 0).g := by
  rw [P.rowHomologyZeroProjection_eq a]
  simp

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. On the included cycles term PC₀,ₐ, the quotient lands only in PH₀,ₐ: rₐ ∘ i_T =
inl ∘ p_C. -/
@[reassoc]
theorem termComponent_f_comp_rowHomologyZeroProjection (a : ℕ) :
    (P.termComponentShortComplex a 0).f ≫
        P.rowHomologyZeroProjection a =
      (P.cyclesComponentShortComplex a 0).g ≫ biprod.inl := by
  apply biprod.hom_ext
  · calc
      ((P.termComponentShortComplex a 0).f ≫
          P.rowHomologyZeroProjection a) ≫ biprod.fst =
        (P.termComponentShortComplex a 0).f ≫
          (P.rowHomologyZeroProjection a ≫ biprod.fst) :=
        Category.assoc _ _ _
      _ = (P.termComponentShortComplex a 0).f ≫
          ((P.termComponentSplitting a 0).r ≫
            (P.cyclesComponentShortComplex a 0).g) := by
        rw [rowHomologyZeroProjection_comp_fst P a]
      _ = ((P.termComponentShortComplex a 0).f ≫
          (P.termComponentSplitting a 0).r) ≫
            (P.cyclesComponentShortComplex a 0).g :=
        (Category.assoc _ _ _).symm
      _ = (P.cyclesComponentShortComplex a 0).g := by
        rw [(P.termComponentSplitting a 0).f_r, Category.id_comp]
      _ = ((P.cyclesComponentShortComplex a 0).g ≫ biprod.inl) ≫
          biprod.fst := by simp
  · calc
      ((P.termComponentShortComplex a 0).f ≫
          P.rowHomologyZeroProjection a) ≫ biprod.snd =
        (P.termComponentShortComplex a 0).f ≫
          (P.rowHomologyZeroProjection a ≫ biprod.snd) :=
        Category.assoc _ _ _
      _ = (P.termComponentShortComplex a 0).f ≫
          (P.termComponentShortComplex a 0).g := by
        rw [rowHomologyZeroProjection_comp_snd P a]
      _ = 0 := (P.termComponentShortComplex a 0).zero
      _ = ((P.cyclesComponentShortComplex a 0).g ≫ biprod.inl) ≫
          biprod.snd := by simp

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The cofork with quotient rₐ is colimiting, so PH₀,ₐ ⊕ PB₀,ₐ is a cokernel of
PB₁,ₐ → PC₀,ₐ → PT₀,ₐ. -/
noncomputable def rowHomologyZeroCompositeCoforkIsColimit (a : ℕ) :
    IsColimit (P.rowHomologyZeroCompositeCofork a) :=
  ShortComplex.Splitting.compLeftCokernelCoforkIsColimit
    (P.cyclesComponentSplitting a 0) (P.termComponentSplitting a 0)

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The same quotient rₐ, together with its universal property, is a selected
cokernel of the actual original-degree differential rowₐ,₁ → rowₐ,₀. -/
noncomputable def rowHomologyZeroCokernelPackage (a : ℕ) :
    Σ c : CokernelCofork ((P.bicomplex.X a).d 1 0), IsColimit c := by
  let _ : Epi ((P.termHorseshoe 1).p.f a) := by
    change Epi (P.termComponentShortComplex a 1).g
    exact (P.termComponentSplitting a 1).epi_g
  have hd : (P.bicomplex.X a).d 1 0 =
      (P.termHorseshoe 1).p.f a ≫
        ((P.cyclesComponentShortComplex a 0).f ≫
          (P.termComponentShortComplex a 0).f) := by
    rw [P.bicomplex_d₂ a 0]
    change (P.termDifferential 0).f a = _
    have h := HomologicalComplex.congr_hom (P.termDifferential_eq 0) a
    simpa only [Nat.zero_add, cyclesComponentShortComplex,
      termComponentShortComplex,
      CartanEilenbergResolution.cyclesShortComplex,
      CartanEilenbergResolution.termShortComplex,
      ShortComplex.map_f, HomologicalComplex.eval_map,
      HomologicalComplex.comp_f, Category.assoc] using h
  have h := isCokernelEpiComp
    (P.rowHomologyZeroCompositeCoforkIsColimit a)
    ((P.termHorseshoe 1).p.f a) hd
  exact ⟨_, h⟩

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The selected cofork of the actual incoming differential (P.bicomplex.Xₐ).d(1,0)
has quotient rₐ and target PH₀,ₐ ⊕ PB₀,ₐ. -/
noncomputable def rowHomologyZeroCofork (a : ℕ) :
    CokernelCofork ((P.bicomplex.X a).d 1 0) :=
  (P.rowHomologyZeroCokernelPackage a).1

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The quotient arrow of the incoming-differential cokernel cofork is exactly the
explicit map rₐ. -/
@[simp]
theorem rowHomologyZeroCofork_π (a : ℕ) :
    (P.rowHomologyZeroCofork a).π =
      P.rowHomologyZeroProjection a := by
  rfl

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The cofork of (P.bicomplex.Xₐ).d(1,0) with quotient rₐ is colimiting, hence
computes the cokernel of the incoming differential. -/
noncomputable def rowHomologyZeroCoforkIsColimit (a : ℕ) :
    IsColimit (P.rowHomologyZeroCofork a) :=
  (P.rowHomologyZeroCokernelPackage a).2

set_option backward.isDefEq.respectTransparency false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. Since the row has no outgoing differential in degree zero, this cokernel defines
right homology data for the row short complex at degrees (1,0,0), with H₀ represented by PH₀,ₐ ⊕
PB₀,ₐ. -/
noncomputable def rowHomologyZeroRightData (a : ℕ) :
    ((P.bicomplex.X a).sc' 1 0 0).RightHomologyData :=
  ShortComplex.RightHomologyData.ofIsColimitCokernelCofork
    ((P.bicomplex.X a).sc' 1 0 0)
      ((P.bicomplex.X a).shape 0 0 (by simp))
      (P.rowHomologyZeroCofork a)
      (P.rowHomologyZeroCoforkIsColimit a)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The degree-zero row homology is canonically isomorphic to PH₀,ₐ ⊕ PB₀,ₐ, with the
explicit quotient rₐ supplying its coordinates. -/
noncomputable def rowHomologyZeroIso (a : ℕ) :
    (P.bicomplex.X a).homology 0 ≅
      (P.homologyResolution 0).complex.X a ⊞
        (P.boundaryResolution 0).complex.X a := by
  change (P.bicomplex.X a).homology 0 ≅
    (P.rowHomologyZeroRightData a).H
  exact (P.bicomplex.X a).homologyIsoSc' 1 0 0 (by simp) (by simp) ≪≫
    (P.rowHomologyZeroRightData a).homologyIso

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The quotient to opcycles of the short complex at (1,0,0), followed by its
right-homology-data opcycles identification, equals rₐ. -/
@[reassoc]
theorem rowHomologyZero_sc_pOpcycles_comp_opcyclesIso (a : ℕ) :
    ((P.bicomplex.X a).sc' 1 0 0).pOpcycles ≫
        (P.rowHomologyZeroRightData a).opcyclesIso.hom =
      P.rowHomologyZeroProjection a := by
  exact (P.rowHomologyZeroRightData a).pOpcycles_comp_opcyclesIso_hom

/-- Let C be abelian, L a chain complex indexed by ℕ and P a Cartan–Eilenberg resolution of L. Write
PBⱼ, PCⱼ, PTⱼ and PHⱼ for its boundary, cycles, term and homology projective resolutions. Fix
resolution degree a. Let r_T : PT₀,ₐ → PC₀,ₐ be the chosen term-horseshoe retraction, and
p_C,p_T its cycle and term quotient maps. The selected quotient is rₐ=(p_C ∘ r_T,p_T) : PT₀,ₐ →
PH₀,ₐ ⊕ PB₀,ₐ. The row's degree-zero opcycles quotient, transported through the canonical
short-complex coordinate identification, is precisely the explicit quotient rₐ. -/
@[reassoc]
theorem rowHomologyZero_pOpcycles_comp_explicitQuotient (a : ℕ) :
    (P.bicomplex.X a).pOpcycles 0 ≫
        ((P.bicomplex.X a).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).hom ≫
        (P.rowHomologyZeroRightData a).opcyclesIso.hom =
      P.rowHomologyZeroProjection a := by
  rw [HomologicalComplex.pOpcycles_opcyclesIsoSc'_hom_assoc]
  exact P.rowHomologyZero_sc_pOpcycles_comp_opcyclesIso a

end HomologicalComplex.CartanEilenbergResolution

end

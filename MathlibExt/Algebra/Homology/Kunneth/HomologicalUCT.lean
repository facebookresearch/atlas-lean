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

public import Mathlib.Algebra.Homology.SingleHomology
public import MathlibExt.Algebra.Homology.Kunneth.Collapse
public import MathlibExt.Algebra.Homology.Kunneth.Naturality
public import MathlibExt.Algebra.Homology.Kunneth.PIDChosen

/-!
# The homological universal coefficient theorem

This file specializes the tensor Künneth theorem to a coefficient module
placed in chain degree zero.  It exposes the canonical coefficient map and,
over a commutative PID, the objectwise short exact sequence

```text
0 → H_n(K) ⊗ A → H_n(K ⊗ A[0])
  → Tor₁(H_(n-1)(K), A) → 0.
```

The left map is canonical and does not depend on a resolution.  The right
map is inherited from the chosen-resolution Künneth sequence, so this file
does not claim naturality, resolution independence, or a splitting.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace HomologicalComplex

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- The Künneth tensor source for coefficients concentrated in degree zero
canonically reduces to `H_n(K) ⊗ A`. -/
noncomputable def homologyUCTTensorSourceIso
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗
        ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology ij.val.2) ≅
      K.homology n ⊗ A := by
  let F : KunnethTensorIndex n → ModuleCat.{u} R := fun ij =>
    K.homology ij.val.1 ⊗
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology ij.val.2
  let j : KunnethTensorIndex n :=
    ⟨(n, 0), Finset.mem_antidiagonal.mpr (by omega)⟩
  have hzero : ∀ k, k ≠ j → IsZero (F k) := by
    intro k hk
    have hsnd : k.val.2 ≠ 0 := by
      intro hsnd
      apply hk
      apply Subtype.ext
      change k.val = (n, 0)
      apply Prod.ext
      · change k.val.1 = n
        have hsum := Finset.mem_antidiagonal.mp k.property
        omega
      · change k.val.2 = 0
        exact hsnd
    apply (tensorLeft (K.homology k.val.1)).map_isZero
    exact isZero_single_obj_homology (ComplexShape.down ℕ) 0 A k.val.2 hsnd
  let e : (⨁ F) ≅ F j :=
    { hom := biproduct.π F j
      inv := biproduct.ι F j
      hom_inv_id := by
        apply biproduct.hom_ext
        intro k
        by_cases hk : k = j
        · subst k
          simp
        · exact (hzero k hk).eq_of_tgt _ _
      inv_hom_id := by simp }
  exact e ≪≫
    tensorIso (Iso.refl _) (singleObjHomologySelfIso
      (ComplexShape.down ℕ) 0 A)

/-- The inverse single-coefficient tensor-source coordinate is natural in
the chain complex and coefficient module. -/
@[reassoc]
theorem homologyUCTTensorSourceIso_inv_naturality
    {R : Type u} [CommRing R]
    {K K' : ChainComplex (ModuleCat.{u} R) ℕ}
    {A A' : ModuleCat.{u} R} (f : K ⟶ K') (a : A ⟶ A') (n : ℕ) :
    (HomologicalComplex.homologyMap f n ⊗ₘ a) ≫
        (homologyUCTTensorSourceIso K' A' n).inv =
      (homologyUCTTensorSourceIso K A n).inv ≫
        kunnethTensorSourceMap f
          ((ChainComplex.single₀ (ModuleCat.{u} R)).map a) n := by
  let j : KunnethTensorIndex n :=
    ⟨(n, 0), Finset.mem_antidiagonal.mpr (by omega)⟩
  apply biproduct.hom_ext
  intro ij
  by_cases hij : ij = j
  · subst ij
    simp only [homologyUCTTensorSourceIso, Iso.trans_inv, tensorIso_inv,
      Iso.refl_inv, id_tensorHom, Category.assoc, bicone_ι_π_self,
      Category.comp_id, kunnethTensorSourceMap, biproduct.ι_map, j]
    rw [← MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp,
      singleObjHomologySelfIso_inv_naturality]
  · have hsnd : ij.val.2 ≠ 0 := by
      intro hsnd
      apply hij
      apply Subtype.ext
      change ij.val = (n, 0)
      apply Prod.ext
      · change ij.val.1 = n
        have hsum := Finset.mem_antidiagonal.mp ij.property
        omega
      · change ij.val.2 = 0
        exact hsnd
    have hzero := isZero_single_obj_homology
      (ComplexShape.down ℕ) 0 A' ij.val.2 hsnd
    have htensor : IsZero (K'.homology ij.val.1 ⊗
        ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A').homology
          ij.val.2) :=
      (tensorLeft (K'.homology ij.val.1)).map_isZero hzero
    exact htensor.eq_of_tgt _ _

/-- The canonical homology map induced by tensoring a chain complex with a
coefficient module in degree zero. -/
noncomputable def homologyUniversalCoefficientMap
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    K.homology n ⊗ A ⟶
      (tensorObj K
        ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A)).homology n :=
  (homologyUCTTensorSourceIso K A n).inv ≫
    kunnethHomologyTensorMap K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) n

/-- The canonical homological universal-coefficient map is the selected
degree-`(n,0)` homology pairing. -/
theorem homologyUniversalCoefficientMap_eq_pairing
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
    homologyUniversalCoefficientMap K A n =
      (𝟙 (K.homology n) ⊗ₘ
          (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 A).inv) ≫
        ChainGradedPairing.pairHomology
          (𝟙 (tensorObj K L))
          (ChainGradedPairing.homologyDescentData
            (𝟙 (tensorObj K L))) n 0 ≫
        (homologyIsoOfEq (tensorObj K L) (Nat.add_zero n)).hom := by
  dsimp only
  unfold homologyUniversalCoefficientMap homologyUCTTensorSourceIso
  simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    id_tensorHom, Category.assoc]
  rw [kunnethHomologyTensorMap_ι]

/-- The canonical homological universal-coefficient map is natural in the
chain complex and coefficient module. -/
@[reassoc]
theorem homologyUniversalCoefficientMap_naturality
    {R : Type u} [CommRing R]
    {K K' : ChainComplex (ModuleCat.{u} R) ℕ}
    {A A' : ModuleCat.{u} R} (f : K ⟶ K') (a : A ⟶ A') (n : ℕ) :
    (HomologicalComplex.homologyMap f n ⊗ₘ a) ≫
        homologyUniversalCoefficientMap K' A' n =
      homologyUniversalCoefficientMap K A n ≫
        HomologicalComplex.homologyMap
          (tensorHom f
            ((ChainComplex.single₀ (ModuleCat.{u} R)).map a)) n := by
  unfold homologyUniversalCoefficientMap
  slice_lhs 1 2 =>
    rw [homologyUCTTensorSourceIso_inv_naturality]
  slice_rhs 2 3 =>
    rw [← kunnethHomologyTensorMap_naturality]
  simp only [Category.assoc]

/-- Over a field, the canonical homological universal-coefficient map is an
isomorphism. -/
theorem isIso_homologyUniversalCoefficientMap_of_field
    {k : Type u} [Field k]
    (K : ChainComplex (ModuleCat.{u} k) ℕ) (A : ModuleCat.{u} k) (n : ℕ) :
    IsIso (homologyUniversalCoefficientMap K A n) := by
  unfold homologyUniversalCoefficientMap
  let _ : IsIso ((homologyUCTTensorSourceIso K A n).inv) := inferInstance
  let _ : IsIso (kunnethHomologyTensorMap K
      ((ChainComplex.single₀ (ModuleCat.{u} k)).obj A) n) :=
    isIso_kunnethHomologyTensorMap_of_field K
      ((ChainComplex.single₀ (ModuleCat.{u} k)).obj A) n
  infer_instance

/-- Over a commutative PID, termwise flatness and torsion-free homology make
the canonical homological universal-coefficient map an isomorphism. -/
theorem isIso_homologyUniversalCoefficientMap_of_pid_of_torsionFree_homology
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ i : ℕ, Module.Flat R (K.X i))
    (hTF : ∀ i : ℕ, Module.IsTorsionFree R (K.homology i))
    (n : ℕ) : IsIso (homologyUniversalCoefficientMap K A n) := by
  unfold homologyUniversalCoefficientMap
  let _ : IsIso ((homologyUCTTensorSourceIso K A n).inv) := inferInstance
  let _ : IsIso (kunnethHomologyTensorMap K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) n) :=
    isIso_kunnethHomologyTensorMap_of_pid_of_torsionFree_homology K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) hK hTF n
  infer_instance

/-- The Tor endpoint in the homological universal coefficient sequence. -/
def homologyUniversalCoefficientTor
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) :
    ℕ → ModuleCat.{u} R
  | 0 => 0
  | q + 1 => ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
      (K.homology q)).obj A

/-- The Künneth Tor-one source for coefficients concentrated in degree zero
canonically reduces to `Tor₁(H_(n-1)(K), A)`, and is zero in degree zero. -/
noncomputable def homologyUCTTorIso
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    (⨁ fun ij : KunnethTorOneIndex n =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology ij.val.1)).obj
          (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology
            ij.val.2)) ≅
      homologyUniversalCoefficientTor K A n := by
  rcases n with _ | q
  · let F : KunnethTorOneIndex 0 → ModuleCat.{u} R := fun ij =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology ij.val.1)).obj
          (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology
            ij.val.2)
    let D := Discrete.functor F
    have hzero : IsZero (⨁ F) := by
      apply (biproduct.isLimit F).isZero_pt
      apply Functor.isZero D
      intro X
      have h := (mem_kunnethTorOneIndex (n := 0) (ij := X.as.val)).mp
        X.as.property
      omega
    exact hzero.isoZero
  · let F : KunnethTorOneIndex (q + 1) → ModuleCat.{u} R := fun ij =>
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology ij.val.1)).obj
          (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology
            ij.val.2)
    let j : KunnethTorOneIndex (q + 1) :=
      ⟨(q, 0), by simp [KunnethTorOneIndex]⟩
    have hzero : ∀ k, k ≠ j → IsZero (F k) := by
      intro k hk
      have hsnd : k.val.2 ≠ 0 := by
        intro hsnd
        apply hk
        apply Subtype.ext
        change k.val = (q, 0)
        apply Prod.ext
        · change k.val.1 = q
          have hsum := (mem_kunnethTorOneIndex (n := q + 1)
            (ij := k.val)).mp k.property
          omega
        · change k.val.2 = 0
          exact hsnd
      have hsingle := isZero_single_obj_homology
        (ComplexShape.down ℕ) 0 A k.val.2 hsnd
      let _ : Projective
          (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology k.val.2) :=
        hsingle.projective
      change IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology k.val.1)).obj
          (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology k.val.2))
      exact CategoryTheory.isZero_Tor_succ_of_projective
        (ModuleCat.{u} R) (K.homology k.val.1)
        (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology k.val.2) 0
    let e : (⨁ F) ≅ F j :=
      { hom := biproduct.π F j
        inv := biproduct.ι F j
        hom_inv_id := by
          apply biproduct.hom_ext
          intro k
          by_cases hk : k = j
          · subst k
            simp
          · exact (hzero k hk).eq_of_tgt _ _
        inv_hom_id := by simp }
    exact e ≪≫
      ((CategoryTheory.Tor (ModuleCat.{u} R) 1).obj
        (K.homology q)).mapIso
          (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 A)

/-- The chosen objectwise PID homological universal-coefficient short complex.

Its left arrow is canonical. Its right arrow uses the repository's chosen
Cartan--Eilenberg resolution of the degree-zero coefficient complex. -/
noncomputable abbrev homologyUniversalCoefficientChosenShortComplex
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) := by
  let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
  let S := kunnethChosenShortComplex K L hK n
  let e₁ := homologyUCTTensorSourceIso K A n
  let e₃ := homologyUCTTorIso K A n
  exact
    { X₁ := K.homology n ⊗ A
      X₂ := (tensorObj K L).homology n
      X₃ := homologyUniversalCoefficientTor K A n
      f := e₁.inv ≫ S.f
      g := S.g ≫ e₃.hom
      zero := by
        rw [Category.assoc, ← Category.assoc S.f, S.zero, zero_comp,
          comp_zero] }

/-- The left arrow in the chosen homological UCT short complex is the
canonical coefficient map. -/
theorem homologyUniversalCoefficientChosenShortComplex_f
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (homologyUniversalCoefficientChosenShortComplex K A hK n).f =
      homologyUniversalCoefficientMap K A n := by
  rfl

/-- The chosen Künneth short complex is isomorphic to the chosen homological
UCT short complex with its textbook endpoints. -/
noncomputable def kunnethChosenShortComplexIsoHomologyUCT
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    kunnethChosenShortComplex K
        ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) hK n ≅
      homologyUniversalCoefficientChosenShortComplex K A hK n := by
  refine ShortComplex.isoMk
    (S₁ := kunnethChosenShortComplex K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) hK n)
    (S₂ := homologyUniversalCoefficientChosenShortComplex K A hK n)
    (homologyUCTTensorSourceIso K A n) (Iso.refl _)
    (homologyUCTTorIso K A n) ?_ ?_
  · simp [homologyUniversalCoefficientChosenShortComplex]
  · simp [homologyUniversalCoefficientChosenShortComplex]

/-- The chosen objectwise homological universal-coefficient short complex
over a commutative PID is exact. -/
theorem homologyUniversalCoefficientChosenShortComplex_shortExact
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) (n : ℕ) :
    (homologyUniversalCoefficientChosenShortComplex K A hK n).ShortExact :=
  ShortComplex.shortExact_of_iso
    (kunnethChosenShortComplexIsoHomologyUCT K A hK n)
    (kunnethChosenShortComplex_shortExact K
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A) hK n)

/-- In degree zero, the canonical homological universal-coefficient map over
a commutative PID is an isomorphism. -/
theorem isIso_homologyUniversalCoefficientMap_zero
    {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)
    (hK : ∀ a : ℕ, Module.Flat R (K.X a)) :
    IsIso (homologyUniversalCoefficientMap K A 0) := by
  let S := homologyUniversalCoefficientChosenShortComplex K A hK 0
  rw [← homologyUniversalCoefficientChosenShortComplex_f K A hK 0]
  have hS := homologyUniversalCoefficientChosenShortComplex_shortExact K A hK 0
  have hzero : IsZero
      (homologyUniversalCoefficientChosenShortComplex K A hK 0).X₃ := by
    change IsZero (0 : ModuleCat.{u} R)
    apply CategoryTheory.Limits.isZero_zero
  exact (hS.isIso_f_iff).2 hzero

end HomologicalComplex

end

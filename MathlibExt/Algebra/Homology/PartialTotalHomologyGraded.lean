/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalHomologyFiltration
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Graded pieces of the partial-total homology filtration

Adjacent cokernel quotients of the partial-total homology filtration
are identified with their finite-stage image coordinates.
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

/-- The finite predecessor used by the increasing homology filtration.  Its
value at zero is the first negative stage, rather than truncated subtraction. -/
def partialTotalHomologyPreviousIndex : ℕ → EInt
  | 0 => ((-1 : ℤ) : EInt)
  | p + 1 => ((p : ℤ) : EInt)

@[simp]
theorem partialTotalHomologyPreviousIndex_zero :
    partialTotalHomologyPreviousIndex 0 = ((-1 : ℤ) : EInt) :=
  rfl

@[simp]
theorem partialTotalHomologyPreviousIndex_succ (p : ℕ) :
    partialTotalHomologyPreviousIndex (p + 1) = ((p : ℤ) : EInt) :=
  rfl

theorem partialTotalHomologyPreviousIndex_le (p : ℕ) :
    partialTotalHomologyPreviousIndex p ≤ ((p : ℤ) : EInt) := by
  rcases p with _ | p <;> simp [partialTotalHomologyPreviousIndex]

/-- The map between consecutive finite stages of the partial-total homology
filtration. -/
noncomputable def partialTotalHomologyFiltrationAdjacentHom (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj
        (partialTotalHomologyPreviousIndex p) ⟶
      (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) :=
  (B.partialTotalHomologyFiltration n).diagram.map
    (homOfLE (partialTotalHomologyPreviousIndex_le p))

/-- The adjacent filtration map commutes with the inclusions into total
homology. -/
@[reassoc (attr := simp)]
theorem partialTotalHomologyFiltrationAdjacentHom_comp_ι (n p : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n p ≫
        (B.partialTotalHomologyFiltration n).ι.app ((p : ℤ) : EInt) =
      (B.partialTotalHomologyFiltration n).ι.app
        (partialTotalHomologyPreviousIndex p) :=
  B.partialTotalHomologyFiltration_map_comp_ι n
    (partialTotalHomologyPreviousIndex_le p)

instance partialTotalHomologyFiltrationAdjacentHom_mono (n p : ℕ) :
    Mono (B.partialTotalHomologyFiltrationAdjacentHom n p) :=
  mono_of_mono_fac
    (B.partialTotalHomologyFiltrationAdjacentHom_comp_ι n p)

/-- The `p`th adjacent graded piece of the increasing homology filtration. -/
noncomputable abbrev partialTotalHomologyGradedPiece (n p : ℕ) : C :=
  cokernel (B.partialTotalHomologyFiltrationAdjacentHom n p)

/-- The quotient map to an adjacent graded piece. -/
noncomputable abbrev partialTotalHomologyGradedπ (n p : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((p : ℤ) : EInt) ⟶
      B.partialTotalHomologyGradedPiece n p :=
  cokernel.π (B.partialTotalHomologyFiltrationAdjacentHom n p)

/-- The adjacent filtration map followed by its cokernel quotient. -/
noncomputable abbrev partialTotalHomologyGradedShortComplex (n p : ℕ) :
    ShortComplex C :=
  ShortComplex.mk
    (B.partialTotalHomologyFiltrationAdjacentHom n p)
    (B.partialTotalHomologyGradedπ n p)
    (cokernel.condition _)

/-- Adjacent filtration stages and their graded quotient form a short exact
sequence. -/
theorem partialTotalHomologyGradedShortComplex_shortExact (n p : ℕ) :
    (B.partialTotalHomologyGradedShortComplex n p).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- Every negative finite stage of the partial-total homology filtration is
zero. -/
theorem isZero_partialTotalHomologyFiltration_obj_of_neg
    (n : ℕ) (z : ℤ) (hz : z < 0) :
    IsZero ((B.partialTotalHomologyFiltration n).obj (z : EInt)) := by
  let H := HomologicalComplex.homologyFunctor C
    (ComplexShape.down ℕ) n
  have hsource : IsZero
      (H.obj (B.partialTotalEIntFiltration.obj (z : EInt))) := by
    change IsZero (H.obj
      (CategoryTheory.Functor.nonnegativeIntObj B.partialTotalFunctor z))
    exact H.map_isZero
      (CategoryTheory.Functor.isZero_nonnegativeIntObj_of_neg
        B.partialTotalFunctor z hz)
  have hzero :
      (B.partialTotalHomologyToTotal n).app (z : EInt) = 0 :=
    hsource.eq_of_src _ _
  change IsZero
    (image ((B.partialTotalHomologyToTotal n).app (z : EInt)))
  exact IsZero.of_iso (isZero_zero C) (imageZero' hzero)

/-- The degree-zero graded quotient map is an isomorphism. -/
theorem isIso_partialTotalHomologyGradedπ_zero (n : ℕ) :
    IsIso (B.partialTotalHomologyGradedπ n 0) := by
  have hS := B.partialTotalHomologyGradedShortComplex_shortExact n 0
  apply (hS.isIso_g_iff).2
  change IsZero ((B.partialTotalHomologyFiltration n).obj
    ((-1 : ℤ) : EInt))
  exact B.isZero_partialTotalHomologyFiltration_obj_of_neg n (-1) (by omega)

/-- The degree-zero filtration step identifies with its graded piece. -/
noncomputable def partialTotalHomologyGradedZeroIso (n : ℕ) :
    (B.partialTotalHomologyFiltration n).obj ((0 : ℤ) : EInt) ≅
      B.partialTotalHomologyGradedPiece n 0 :=
  let _ : IsIso (B.partialTotalHomologyGradedπ n 0) :=
    B.isIso_partialTotalHomologyGradedπ_zero n
  asIso (B.partialTotalHomologyGradedπ n 0)

/-- In homological degree `n`, every filtration inclusion at a stage at least
`n` is an isomorphism. -/
theorem partialTotalHomologyFiltration_ι_app_isIso_of_degree_le
    (n : ℕ) (a : EInt) (h : ((n : ℤ) : EInt) ≤ a) :
    IsIso ((B.partialTotalHomologyFiltration n).ι.app a) := by
  let f := (B.partialTotalHomologyFiltration n).diagram.map (homOfLE h)
  let g := (B.partialTotalHomologyFiltration n).ι.app a
  let _ : IsIso ((B.partialTotalHomologyFiltration n).ι.app
      ((n : ℤ) : EInt)) :=
    B.partialTotalHomologyFiltration_exhaustive_at_degree n
  have hfac : f ≫ g =
      (B.partialTotalHomologyFiltration n).ι.app ((n : ℤ) : EInt) :=
    B.partialTotalHomologyFiltration_map_comp_ι n h
  have hEpi : Epi g := epi_of_epi_fac hfac
  let _ : Epi g := hEpi
  exact isIso_of_mono_of_epi g

/-- Above the total degree, adjacent filtration maps are isomorphisms. -/
theorem isIso_partialTotalHomologyFiltrationAdjacentHom_of_degree_lt
    (n p : ℕ) (h : n < p) :
    IsIso (B.partialTotalHomologyFiltrationAdjacentHom n p) := by
  rcases p with _ | p
  · omega
  · let _ : IsIso ((B.partialTotalHomologyFiltration n).ι.app
        (partialTotalHomologyPreviousIndex (p + 1))) := by
      rw [partialTotalHomologyPreviousIndex_succ]
      exact B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le n _ (by
        simp only [WithBotTop.coe_le_coe]
        exact_mod_cast Nat.le_of_lt_succ h)
    let _ : IsIso ((B.partialTotalHomologyFiltration n).ι.app
        (((p + 1 : ℕ) : ℤ) : EInt)) :=
      B.partialTotalHomologyFiltration_ι_app_isIso_of_degree_le n _ (by
        simp only [WithBotTop.coe_le_coe]
        exact_mod_cast Nat.le_of_lt h)
    exact IsIso.of_isIso_fac_right
      (B.partialTotalHomologyFiltrationAdjacentHom_comp_ι n (p + 1))

/-- Graded pieces strictly above the total degree vanish. -/
theorem isZero_partialTotalHomologyGradedPiece_of_degree_lt
    (n p : ℕ) (h : n < p) :
    IsZero (B.partialTotalHomologyGradedPiece n p) := by
  let _ : IsIso (B.partialTotalHomologyFiltrationAdjacentHom n p) :=
    B.isIso_partialTotalHomologyFiltrationAdjacentHom_of_degree_lt n p h
  exact isZero_cokernel_of_epi
    (B.partialTotalHomologyFiltrationAdjacentHom n p)

/-- Homology of a partial-total transition followed by the inclusion into the
full total is the earlier inclusion. -/
@[reassoc]
theorem partialTotalHomologyMap_comp_partialTotalι
    (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    HomologicalComplex.homologyMap (B.partialTotalMap h) n ≫
        HomologicalComplex.homologyMap (B.partialTotalι p') n =
      HomologicalComplex.homologyMap (B.partialTotalι p) n := by
  rw [← HomologicalComplex.homologyMap_comp,
    B.partialTotalMap_comp_partialTotalι h]

/-- The map between finite-stage homology images induced by a partial-total
filtration map. -/
noncomputable def partialTotalHomologyFiltrationImageMap
    (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    image (HomologicalComplex.homologyMap (B.partialTotalι p) n) ⟶
      image (HomologicalComplex.homologyMap (B.partialTotalι p') n) :=
  (image.eqToIso
    (B.partialTotalHomologyMap_comp_partialTotalι n h).symm).hom ≫
  image.preComp
    (HomologicalComplex.homologyMap (B.partialTotalMap h) n)
    (HomologicalComplex.homologyMap (B.partialTotalι p') n)

/-- The finite-stage image map commutes with the inclusions into total
homology. -/
@[reassoc]
theorem partialTotalHomologyFiltrationImageMap_comp_ι
    (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalHomologyFiltrationImageMap n h ≫
        image.ι (HomologicalComplex.homologyMap
          (B.partialTotalι p') n) =
      image.ι (HomologicalComplex.homologyMap
        (B.partialTotalι p) n) := by
  dsimp only [partialTotalHomologyFiltrationImageMap]
  rw [Category.assoc, image.preComp_ι]
  exact (image.eq_fac
    (B.partialTotalHomologyMap_comp_partialTotalι n h).symm).symm

/-- The finite-stage image coordinates intertwine the filtration map and the
map induced on images. -/
theorem partialTotalHomologyFiltrationObjIsoImage_naturality
    (n : ℕ) {p p' : ℕ} (h : p ≤ p') :
    (B.partialTotalHomologyFiltration n).diagram.map
          (homOfLE (show ((p : ℤ) : EInt) ≤
            ((p' : ℤ) : EInt) by simpa using h)) ≫
        (B.partialTotalHomologyFiltrationObjIsoImage n p').hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n p).hom ≫
        B.partialTotalHomologyFiltrationImageMap n h := by
  apply (cancel_mono
    (image.ι (HomologicalComplex.homologyMap
      (B.partialTotalι p') n))).1
  simp only [Category.assoc]
  rw [B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι n p',
    B.partialTotalHomologyFiltrationImageMap_comp_ι n h,
    B.partialTotalHomologyFiltrationObjIsoImage_hom_comp_ι n p,
    B.partialTotalHomologyFiltration_map_comp_ι]

/-- At a successor index, the adjacent map is the literal map between the two
corresponding finite filtration stages. -/
theorem partialTotalHomologyFiltrationAdjacentHom_succ (n p : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n (p + 1) =
      (B.partialTotalHomologyFiltration n).diagram.map
        (homOfLE (show ((p : ℤ) : EInt) ≤
          (((p + 1 : ℕ) : ℤ) : EInt) by simp)) := by
  apply (B.partialTotalHomologyFiltration n).diagram.congr_map
  subsingleton

/-- In image coordinates, the successor adjacent filtration map is the map
induced between successive partial-total homology images. -/
@[reassoc]
theorem
    partialTotalHomologyFiltrationAdjacentHom_succ_comp_objIsoImage_hom
    (n m : ℕ) :
    B.partialTotalHomologyFiltrationAdjacentHom n (m + 1) ≫
        (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1)).hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n m).hom ≫
        B.partialTotalHomologyFiltrationImageMap n (Nat.le_succ m) := by
  rw [B.partialTotalHomologyFiltrationAdjacentHom_succ n m]
  exact B.partialTotalHomologyFiltrationObjIsoImage_naturality n
    (Nat.le_succ m)

/-- A successor graded piece is the cokernel of the corresponding map of
finite-stage images. -/
noncomputable def partialTotalHomologyGradedPieceSuccIsoImageCokernel
    (n m : ℕ) :
    B.partialTotalHomologyGradedPiece n (m + 1) ≅
      cokernel (B.partialTotalHomologyFiltrationImageMap n
        (Nat.le_succ m)) :=
  cokernel.mapIso
    (f := B.partialTotalHomologyFiltrationAdjacentHom n (m + 1))
    (B.partialTotalHomologyFiltrationImageMap n (Nat.le_succ m))
    (B.partialTotalHomologyFiltrationObjIsoImage n m)
    (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1))
    (B.partialTotalHomologyFiltrationAdjacentHom_succ_comp_objIsoImage_hom
      n m)

/-- The successor graded quotient agrees with the cokernel quotient in image
coordinates. -/
@[reassoc]
theorem partialTotalHomologyGradedπ_comp_succIsoImageCokernel_hom
    (n m : ℕ) :
    B.partialTotalHomologyGradedπ n (m + 1) ≫
        (B.partialTotalHomologyGradedPieceSuccIsoImageCokernel n m).hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1)).hom ≫
        cokernel.π (B.partialTotalHomologyFiltrationImageMap n
          (Nat.le_succ m)) := by
  dsimp only [partialTotalHomologyGradedPieceSuccIsoImageCokernel]
  change cokernel.π
        (B.partialTotalHomologyFiltrationAdjacentHom n (m + 1)) ≫
      cokernel.map
        (B.partialTotalHomologyFiltrationAdjacentHom n (m + 1))
        (B.partialTotalHomologyFiltrationImageMap n (Nat.le_succ m))
        (B.partialTotalHomologyFiltrationObjIsoImage n m).hom
        (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1)).hom
        (B.partialTotalHomologyFiltrationAdjacentHom_succ_comp_objIsoImage_hom
          n m) =
    (B.partialTotalHomologyFiltrationObjIsoImage n (m + 1)).hom ≫
      cokernel.π
        (B.partialTotalHomologyFiltrationImageMap n (Nat.le_succ m))
  apply cokernel.π_desc

/-- The degree-zero graded piece is the image of the degree-zero partial-total
homology map. -/
noncomputable def partialTotalHomologyGradedPieceZeroIsoImage (n : ℕ) :
    B.partialTotalHomologyGradedPiece n 0 ≅
      image (HomologicalComplex.homologyMap (B.partialTotalι 0) n) :=
  (B.partialTotalHomologyGradedZeroIso n).symm ≪≫
    B.partialTotalHomologyFiltrationObjIsoImage n 0

/-- The degree-zero quotient followed by the image coordinate is the existing
filtration-step image coordinate. -/
@[reassoc]
theorem partialTotalHomologyGradedπ_zero_comp_zeroIsoImage_hom (n : ℕ) :
    B.partialTotalHomologyGradedπ n 0 ≫
        (B.partialTotalHomologyGradedPieceZeroIsoImage n).hom =
      (B.partialTotalHomologyFiltrationObjIsoImage n 0).hom := by
  change (B.partialTotalHomologyGradedZeroIso n).hom ≫
      (B.partialTotalHomologyGradedZeroIso n).inv ≫
        (B.partialTotalHomologyFiltrationObjIsoImage n 0).hom = _
  simp only [Iso.hom_inv_id_assoc]

end HomologicalComplex₂

end

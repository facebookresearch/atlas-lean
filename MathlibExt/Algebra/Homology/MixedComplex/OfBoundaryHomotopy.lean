/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.ConnesConstruction

/-!
# Mixed complexes from square-zero boundary homotopies

The square-zero components of a degree-one homotopy from zero to zero
define a mixed complex. The homotopy equation gives anticommutation with
the differential, including degree zero. The associated signed-column
bicomplex agrees with the homotopy bicomplex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MixedComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K : ChainComplex C ℕ) (H : Homotopy (0 : K ⟶ K) 0)
  (hH : ∀ n : ℕ, H.hom n (n + 1) ≫ H.hom (n + 1) (n + 2) = 0)

/-- The square-zero components of a homotopy from zero to zero define a mixed complex. -/
def ofBoundaryHomotopy : MixedComplex C where
  underlying := K
  B n := H.hom n (n + 1)
  B_sq := hH
  B_b_zero := by
    have h := H.comm 0
    rw [HomologicalComplex.zero_f_apply, add_zero,
      dNext_eq_zero H.hom 0 (by simp), zero_add,
      prevD_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel 1 0)] at h
    exact h.symm
  anticomm n := by
    have h := H.comm (n + 1)
    rw [HomologicalComplex.zero_f_apply, add_zero,
      dNext_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq H.hom (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
    exact (add_comm _ _).trans h.symm

/-- The constructed mixed complex retains the whole original chain complex. -/
@[simp]
theorem ofBoundaryHomotopy_underlying : (ofBoundaryHomotopy K H hH).underlying = K := rfl

/-- Every mixed component is the original relevant homotopy component. -/
@[simp]
theorem ofBoundaryHomotopy_B (n : ℕ) :
    (ofBoundaryHomotopy K H hH).B n = H.hom n (n + 1) := rfl

/-- Canonical packaging preserves the entire original zero homotopy, including
its zero off-shape components. -/
theorem ofBoundaryHomotopy_boundaryHomotopy :
    (ofBoundaryHomotopy K H hH).boundaryHomotopy = H := by
  apply Homotopy.ext
  funext i j
  by_cases hij : (ComplexShape.down ℕ).Rel j i
  · have hj : j = i + 1 := by change i + 1 = j at hij; omega
    subst j
    exact (ofBoundaryHomotopy K H hH).boundaryHomotopy_hom i
  · rw [(ofBoundaryHomotopy K H hH).boundaryHomotopy.zero i j hij, H.zero i j hij]
    rfl

section Maps

variable {K} {L : ChainComplex C ℕ}
  (H' : Homotopy (0 : L ⟶ L) 0)
  (hH' : ∀ n : ℕ, H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0)
  (f : K ⟶ L)
  (hf : ∀ n : ℕ, f.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ f.f (n + 1))

/-- An original chain map compatible with the original degree-one components
is the morphism between the constructed mixed complexes. -/
def ofBoundaryHomotopyMap :
    ofBoundaryHomotopy K H hH ⟶ ofBoundaryHomotopy L H' hH' where
  underlying := f
  comm_B' := hf

/-- The constructed mixed-complex map keeps the original whole chain map. -/
@[simp]
theorem ofBoundaryHomotopyMap_underlying :
    (ofBoundaryHomotopyMap H hH H' hH' f hf).underlying = f := rfl

end Maps

/-- The identity chain map induces the identity mixed-complex map. -/
@[simp]
theorem ofBoundaryHomotopyMap_id :
    ofBoundaryHomotopyMap H hH H hH (𝟙 K)
      (fun n => by simp only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id]) =
        𝟙 (ofBoundaryHomotopy K H hH) := by
  apply MixedComplex.hom_ext
  rfl

/-- Composition retains the original chain-map composition and derives its
mixed compatibility from the two original compatibility equations. -/
theorem ofBoundaryHomotopyMap_comp {L T : ChainComplex C ℕ}
    (H' : Homotopy (0 : L ⟶ L) 0)
    (hH' : ∀ n : ℕ, H'.hom n (n + 1) ≫ H'.hom (n + 1) (n + 2) = 0)
    (H'' : Homotopy (0 : T ⟶ T) 0)
    (hH'' : ∀ n : ℕ, H''.hom n (n + 1) ≫ H''.hom (n + 1) (n + 2) = 0)
    (f : K ⟶ L) (g : L ⟶ T)
    (hf : ∀ n : ℕ, f.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ f.f (n + 1))
    (hg : ∀ n : ℕ, g.f n ≫ H''.hom n (n + 1) = H'.hom n (n + 1) ≫ g.f (n + 1)) :
    ofBoundaryHomotopyMap H hH H'' hH'' (f ≫ g) (fun n => by
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
        hg n, ← Category.assoc, hf n, Category.assoc]) =
      ofBoundaryHomotopyMap H hH H' hH' f hf ≫
        ofBoundaryHomotopyMap H' hH' H'' hH'' g hg := by
  apply MixedComplex.hom_ext
  rfl

section Homology

variable (n : ℕ) [K.HasHomology n] [K.HasHomology (n + 1)]

local instance ofBoundaryHomotopy_hasHomology :
    (ofBoundaryHomotopy K H hH).underlying.HasHomology n := by
  dsimp only [ofBoundaryHomotopy]
  infer_instance

local instance ofBoundaryHomotopy_hasHomology_succ :
    (ofBoundaryHomotopy K H hH).underlying.HasHomology (n + 1) := by
  dsimp only [ofBoundaryHomotopy]
  infer_instance

/-- The induced cycle operator is the original native homotopy cycle map. -/
theorem ofBoundaryHomotopy_cyclesB :
    (ofBoundaryHomotopy K H hH).cyclesB n =
      H.cyclesDegreeMap (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) := by
  apply (cancel_mono (K.iCycles (n + 1))).1
  calc
    _ = K.iCycles n ≫ H.hom n (n + 1) := by
      simpa only [ofBoundaryHomotopy_underlying, ofBoundaryHomotopy_B] using
        (ofBoundaryHomotopy K H hH).cyclesB_iCycles n
    _ = _ := (H.cyclesDegreeMap_i (i := n) (j := n + 1)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)).symm

/-- The induced homology operator is the original native homotopy homology map. -/
theorem ofBoundaryHomotopy_homologyB :
    (ofBoundaryHomotopy K H hH).homologyB n =
      H.homologyDegreeMap (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) := by
  apply (cancel_epi (K.homologyπ n)).1
  have hCanonical :
      K.homologyπ n ≫ (ofBoundaryHomotopy K H hH).homologyB n =
        (ofBoundaryHomotopy K H hH).cyclesB n ≫ K.homologyπ (n + 1) := by
    simpa only [ofBoundaryHomotopy_underlying] using
      (ofBoundaryHomotopy K H hH).homologyπ_homologyB n
  rw [ofBoundaryHomotopy_cyclesB K H hH n] at hCanonical
  exact hCanonical.trans
    (H.homologyπ_homologyDegreeMap (i := n) (j := n + 1)
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)).symm

end Homology

section Bicomplex

variable [HasZeroObject C]

/-- The canonical Connes bicomplex is the original signed-column construction. -/
theorem ofBoundaryHomotopy_connesBicomplex :
    (ofBoundaryHomotopy K H hH).connesBicomplex = ChainComplex.mixedBicomplex K H hH := by
  let H₀ : Homotopy (0 : K ⟶ K) 0 := (ofBoundaryHomotopy K H hH).boundaryHomotopy
  have hEq : H₀ = H := ofBoundaryHomotopy_boundaryHomotopy K H hH
  have hSquare : ∀ n : ℕ, H₀.hom n (n + 1) ≫ H₀.hom (n + 1) (n + 2) = 0 := by
    intro n
    simpa only [H₀, boundaryHomotopy_hom, ofBoundaryHomotopy_B] using hH n
  have hCompare : ∀ (J : Homotopy (0 : K ⟶ K) 0)
      (hJ : ∀ n : ℕ, J.hom n (n + 1) ≫ J.hom (n + 1) (n + 2) = 0),
      J = H → ChainComplex.mixedBicomplex K J hJ = ChainComplex.mixedBicomplex K H hH := by
    intro J hJ h
    cases h
    rfl
  change ChainComplex.mixedBicomplex K H₀ hSquare = ChainComplex.mixedBicomplex K H hH
  exact hCompare H₀ hSquare hEq

/-- Connes data on the signed-column bicomplex of a square-zero boundary homotopy. -/
def ofBoundaryHomotopyConnesDoubleData : ConnesDoubleData (ofBoundaryHomotopy K H hH) where
  K := ChainComplex.mixedBicomplex K H hH
  objIso p q hpq := ChainComplex.mixedBicomplexCellIso K H hH p q hpq
  isZero p q hpq := ChainComplex.mixedBicomplex_isZero_cell K H hH p q hpq
  vertical_spec p q hpq hpq' := by
    have h := (ofBoundaryHomotopy K H hH).connesDoubleData.vertical_spec p q hpq hpq'
    simpa only [connesDoubleData, connesBicomplexCellIso, connesBicomplex,
      ofBoundaryHomotopy_underlying, ChainComplex.mixedBicomplex,
      ChainComplex.mixedBicomplexCellIso] using h
  horizontal_spec p q hpq hpq' := by
    have h := (ofBoundaryHomotopy K H hH).connesDoubleData.horizontal_spec p q hpq hpq'
    simpa only [connesDoubleData, connesBicomplexCellIso, connesBicomplex,
      ofBoundaryHomotopy_underlying, ofBoundaryHomotopy_boundaryHomotopy,
      ofBoundaryHomotopy_B, ChainComplex.mixedBicomplex,
      ChainComplex.mixedBicomplexCellIso, ChainComplex.of_d, ChainComplex.mixedHorizontalMap_f,
      ChainComplex.mixedHorizontalComponent, dif_pos hpq, boundaryHomotopy_hom] using h

/-- The compatibility data retain the complete original bicomplex definition. -/
@[simp]
theorem ofBoundaryHomotopyConnesDoubleData_K :
    (ofBoundaryHomotopyConnesDoubleData K H hH).K = ChainComplex.mixedBicomplex K H hH := rfl

/-- The identity on the degree objects identifies the two original
constructions; no comparison is a caller input. -/
def ofBoundaryHomotopyConnesIso :
    (ofBoundaryHomotopy K H hH).connesBicomplex ≅ ChainComplex.mixedBicomplex K H hH :=
  eqToIso (ofBoundaryHomotopy_connesBicomplex K H hH)

/-- The comparison is the identity in every original cell. -/
@[simp]
theorem ofBoundaryHomotopyConnesIso_hom_f_f (p q : ℕ) :
    (((ofBoundaryHomotopyConnesIso K H hH).hom).f p).f q = 𝟙 _ := by
  change ((eqToHom (ofBoundaryHomotopy_connesBicomplex K H hH)).f p).f q = _
  simp only [HomologicalComplex.eqToHom_f]
  let T : C := (ChainComplex.mixedColumn K p).X q
  have hCell : T = T := congrArg
    (fun B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) => (B.X p).X q)
    (ofBoundaryHomotopy_connesBicomplex K H hH)
  change eqToHom hCell = 𝟙 T
  exact eqToHom_refl T hCell

/-- The inverse comparison is also the identity in every original cell. -/
@[simp]
theorem ofBoundaryHomotopyConnesIso_inv_f_f (p q : ℕ) :
    (((ofBoundaryHomotopyConnesIso K H hH).inv).f p).f q = 𝟙 _ := by
  change ((eqToHom (ofBoundaryHomotopy_connesBicomplex K H hH).symm).f p).f q = _
  simp only [HomologicalComplex.eqToHom_f]
  let T : C := (ChainComplex.mixedColumn K p).X q
  have hCell : T = T := congrArg
    (fun B : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) => (B.X p).X q)
    (ofBoundaryHomotopy_connesBicomplex K H hH).symm
  change eqToHom hCell = 𝟙 T
  exact eqToHom_refl T hCell

end Bicomplex

end MixedComplex

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Positive tails and homology

The positive tail sends degree `n` to degree `n + 1` of the given complex.
If the boundary from degree one to degree zero vanishes, the cokernel of
`d 2 1` identifies the tail's degree-zero homology with degree-one homology
of the original complex. Positive degrees use the corresponding shifted
short complexes. The comparisons preserve cycle inclusions and homology
projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- The actual nonnegative chain complex with degree `n` equal to original degree `n+1`. -/
def positiveTail (K : ChainComplex C ℕ) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => K.X (n + 1))
    (fun n => K.d (n + 2) (n + 1)) (fun _ => by simp)

@[simp]
theorem positiveTail_X (K : ChainComplex C ℕ) (n : ℕ) : (positiveTail K).X n = K.X (n + 1) := rfl

@[simp]
theorem positiveTail_d_succ (K : ChainComplex C ℕ) (n : ℕ) :
    (positiveTail K).d (n + 1) n = K.d (n + 2) (n + 1) := by
  simp only [positiveTail, ChainComplex.of_d]

/-- Actual chain maps restrict functorially to the actual positive tails. -/
def positiveTailMap {K L : ChainComplex C ℕ} (f : K ⟶ L) : positiveTail K ⟶ positiveTail L :=
  ChainComplex.ofHom (fun n => f.f (n + 1))
    (fun n => by
      rw [positiveTail_d_succ, positiveTail_d_succ]
      exact f.comm (n + 2) (n + 1))

@[simp]
theorem positiveTailMap_f {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    (positiveTailMap f).f n = f.f (n + 1) := rfl

@[simp]
theorem positiveTailMap_id (K : ChainComplex C ℕ) : positiveTailMap (𝟙 K) = 𝟙 (positiveTail K) := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

theorem positiveTailMap_comp {K L M : ChainComplex C ℕ} (f : K ⟶ L) (g : L ⟶ M) :
    positiveTailMap (f ≫ g) = positiveTailMap f ≫ positiveTailMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

end

section

variable [Abelian C]

/-- Every positive-tail row above degree zero is the original shifted row. -/
def positiveTailRowIso (K : ChainComplex C ℕ) (n : ℕ) :
    (positiveTail K).sc' (n + 2) (n + 1) n ≅ K.sc' (n + 3) (n + 2) (n + 1) :=
  ShortComplex.isoMk (eqToIso (by rfl)) (eqToIso (by rfl)) (eqToIso (by rfl))
    (by
      change 𝟙 (K.X (n + 3)) ≫ K.d (n + 3) (n + 2) =
        (positiveTail K).d (n + 2) (n + 1) ≫ 𝟙 (K.X (n + 2))
      exact (Category.id_comp _).trans
        ((positiveTail_d_succ K (n + 1)).symm.trans (Category.comp_id _).symm))
    (by
      change 𝟙 (K.X (n + 2)) ≫ K.d (n + 2) (n + 1) =
        (positiveTail K).d (n + 1) n ≫ 𝟙 (K.X (n + 1))
      exact (Category.id_comp _).trans
        ((positiveTail_d_succ K n).symm.trans (Category.comp_id _).symm))

/-- At degree zero the tail cycles and homology use the native cokernel data. -/
def positiveTailZeroData (K : ChainComplex C ℕ) :
    ((positiveTail K).sc' 1 0 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofHasCokernel _ (by
    change (positiveTail K).d 0 0 = 0
    exact (positiveTail K).shape 0 0 (by decide))

/-- When the original degree-one differential vanishes, its native data
uses the original cokernel of the incoming differential. -/
def originalOneData (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    (K.sc' 2 1 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofHasCokernel _ hK

/-- The native cokernel comparison follows from the actual tail differential. -/
def positiveTailZeroCokernelIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    (positiveTailZeroData K).H ≅ (originalOneData K hK).H := by
  exact cokernel.mapIso ((positiveTail K).sc' 1 0 0).f (K.d 2 1)
    (eqToIso (by rfl)) (eqToIso (by rfl)) (by
      change (positiveTail K).d 1 0 ≫ 𝟙 (K.X 1) = 𝟙 (K.X 2) ≫ K.d 2 1
      exact (Category.comp_id _).trans
        ((positiveTail_d_succ K 0).trans (Category.id_comp _).symm))

private theorem positiveTailZeroCokernelIso_π (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    (positiveTailZeroData K).π ≫ (positiveTailZeroCokernelIso K hK).hom =
      (originalOneData K hK).π := by
  change cokernel.π ((positiveTail K).sc' 1 0 0).f ≫
      cokernel.desc ((positiveTail K).sc' 1 0 0).f
        (𝟙 (K.X 1) ≫ cokernel.π (K.d 2 1)) _ = cokernel.π (K.d 2 1)
  exact (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- Cycles of every explicit tail row identify with the original shifted cycles. -/
def positiveTailExplicitCyclesIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    ∀ n : ℕ, ((positiveTail K).sc' (n + 1) n (n - 1)).cycles ≅
      (K.sc' (n + 2) (n + 1) n).cycles
  | 0 => (positiveTailZeroData K).cyclesIso ≪≫ (originalOneData K hK).cyclesIso.symm
  | n + 1 => by
      exact ShortComplex.cyclesMapIso (positiveTailRowIso K n)

/-- Homology of every explicit tail row identifies with the original shifted homology. -/
def positiveTailExplicitHomologyIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    ∀ n : ℕ, ((positiveTail K).sc' (n + 1) n (n - 1)).homology ≅
      (K.sc' (n + 2) (n + 1) n).homology
  | 0 => (positiveTailZeroData K).homologyIso ≪≫
      positiveTailZeroCokernelIso K hK ≪≫ (originalOneData K hK).homologyIso.symm
  | n + 1 => by
      exact ShortComplex.homologyMapIso (positiveTailRowIso K n)

private theorem positiveTailExplicitCyclesIso_i (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0)
    (n : ℕ) :
    (positiveTailExplicitCyclesIso K hK n).hom ≫ (K.sc' (n + 2) (n + 1) n).iCycles =
      ((positiveTail K).sc' (n + 1) n (n - 1)).iCycles := by
  cases n with
  | zero =>
      let D₀ := positiveTailZeroData K
      let D₁ := originalOneData K hK
      change (D₀.cyclesIso.hom ≫ D₁.cyclesIso.inv) ≫ (K.sc' 2 1 0).iCycles =
        ((positiveTail K).sc' 1 0 0).iCycles
      have h₁ : D₁.cyclesIso.inv ≫ (K.sc' 2 1 0).iCycles = 𝟙 (K.X 1) :=
        D₁.cyclesIso_inv_comp_iCycles
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => D₀.cyclesIso.hom ≫ z) h₁).trans
          D₀.cyclesIso_hom_comp_i)
  | succ n =>
      change ShortComplex.cyclesMap (positiveTailRowIso K n).hom ≫
        (K.sc' (n + 3) (n + 2) (n + 1)).iCycles =
          ((positiveTail K).sc' (n + 2) (n + 1) n).iCycles
      exact (ShortComplex.cyclesMap_i (positiveTailRowIso K n).hom).trans
        (Category.comp_id _)

private theorem positiveTailExplicitHomologyIso_π (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0)
    (n : ℕ) :
    (positiveTailExplicitCyclesIso K hK n).hom ≫ (K.sc' (n + 2) (n + 1) n).homologyπ =
      ((positiveTail K).sc' (n + 1) n (n - 1)).homologyπ ≫
        (positiveTailExplicitHomologyIso K hK n).hom := by
  cases n with
  | zero =>
      let D₀ := positiveTailZeroData K
      let D₁ := originalOneData K hK
      let κ := positiveTailZeroCokernelIso K hK
      have hκ : D₀.π ≫ κ.hom = D₁.π := positiveTailZeroCokernelIso_π K hK
      change (D₀.cyclesIso.hom ≫ D₁.cyclesIso.inv) ≫ (K.sc' 2 1 0).homologyπ =
        ((positiveTail K).sc' 1 0 0).homologyπ ≫
          (D₀.homologyIso.hom ≫ κ.hom ≫ D₁.homologyIso.inv)
      calc
        _ = D₀.cyclesIso.hom ≫ (D₁.π ≫ D₁.homologyIso.inv) :=
          (Category.assoc _ _ _).trans
            (congrArg (fun z => D₀.cyclesIso.hom ≫ z) D₁.π_comp_homologyIso_inv.symm)
        _ = D₀.cyclesIso.hom ≫ ((D₀.π ≫ κ.hom) ≫ D₁.homologyIso.inv) :=
          congrArg (fun z => D₀.cyclesIso.hom ≫ (z ≫ D₁.homologyIso.inv)) hκ.symm
        _ = (D₀.cyclesIso.hom ≫ D₀.π) ≫ κ.hom ≫ D₁.homologyIso.inv := by
          simp only [Category.assoc]
        _ = (((positiveTail K).sc' 1 0 0).homologyπ ≫ D₀.homologyIso.hom) ≫
            κ.hom ≫ D₁.homologyIso.inv :=
          congrArg (fun z => z ≫ κ.hom ≫ D₁.homologyIso.inv)
            D₀.homologyπ_comp_homologyIso_hom.symm
        _ = _ := by simp only [Category.assoc]
  | succ n =>
      change ShortComplex.cyclesMap (positiveTailRowIso K n).hom ≫
        (K.sc' (n + 3) (n + 2) (n + 1)).homologyπ =
        ((positiveTail K).sc' (n + 2) (n + 1) n).homologyπ ≫
          ShortComplex.homologyMap (positiveTailRowIso K n).hom
      exact (ShortComplex.homologyπ_naturality (positiveTailRowIso K n).hom).symm

/-- The actual positive-tail cycles identify with the original cycles one degree higher. -/
def positiveTailCyclesIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTail K).cycles n ≅ K.cycles (n + 1) :=
  (positiveTail K).cyclesIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    positiveTailExplicitCyclesIso K hK n ≪≫
      (K.cyclesIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).symm

/-- The actual positive-tail homology identifies with the original native homology one degree higher. -/
def positiveTailHomologyIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTail K).homology n ≅ K.homology (n + 1) :=
  (positiveTail K).homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    positiveTailExplicitHomologyIso K hK n ≪≫
      (K.homologyIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).symm

/-- The cycles comparison is pinned by the actual native inclusion into original degree `n+1`. -/
theorem positiveTailCyclesIso_i (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailCyclesIso K hK n).hom ≫ K.iCycles (n + 1) = (positiveTail K).iCycles n := by
  simp only [positiveTailCyclesIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles, positiveTailExplicitCyclesIso_i]
  exact HomologicalComplex.cyclesIsoSc'_hom_iCycles _ _ _ _ _ _

/-- The homology comparison is pinned by the actual epic cycle projection. -/
theorem positiveTailHomologyIso_π (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailCyclesIso K hK n).hom ≫ K.homologyπ (n + 1) =
      (positiveTail K).homologyπ n ≫ (positiveTailHomologyIso K hK n).hom := by
  let T := positiveTail K
  let S₀ := T.sc' (n + 1) n (n - 1)
  let S₁ := K.sc' (n + 2) (n + 1) n
  let eC₀ := T.cyclesIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
  let eH₀ := T.homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)
  let eC₁ := K.cyclesIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)
  let eH₁ := K.homologyIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)
  let rC := positiveTailExplicitCyclesIso K hK n
  let rH := positiveTailExplicitHomologyIso K hK n
  have h₁ : eC₁.inv ≫ K.homologyπ (n + 1) = S₁.homologyπ ≫ eH₁.inv :=
    (HomologicalComplex.π_homologyIsoSc'_inv K (n + 2) (n + 1) n
      (by simp [Nat.add_assoc]) (by simp)).symm
  have h₂ : rC.hom ≫ S₁.homologyπ = S₀.homologyπ ≫ rH.hom :=
    positiveTailExplicitHomologyIso_π K hK n
  have h₃ : T.homologyπ n ≫ eH₀.hom = eC₀.hom ≫ S₀.homologyπ :=
    HomologicalComplex.π_homologyIsoSc'_hom T (n + 1) n (n - 1)
      (by simp) (by cases n <;> simp)
  change (eC₀.hom ≫ rC.hom ≫ eC₁.inv) ≫ K.homologyπ (n + 1) =
    T.homologyπ n ≫ eH₀.hom ≫ rH.hom ≫ eH₁.inv
  calc
    _ = eC₀.hom ≫ rC.hom ≫ (eC₁.inv ≫ K.homologyπ (n + 1)) := by
      simp only [Category.assoc]
    _ = eC₀.hom ≫ rC.hom ≫ (S₁.homologyπ ≫ eH₁.inv) :=
      congrArg (fun z => eC₀.hom ≫ rC.hom ≫ z) h₁
    _ = eC₀.hom ≫ (rC.hom ≫ S₁.homologyπ) ≫ eH₁.inv := by
      simp only [Category.assoc]
    _ = eC₀.hom ≫ (S₀.homologyπ ≫ rH.hom) ≫ eH₁.inv :=
      congrArg (fun z => eC₀.hom ≫ z ≫ eH₁.inv) h₂
    _ = (eC₀.hom ≫ S₀.homologyπ) ≫ rH.hom ≫ eH₁.inv := by
      simp only [Category.assoc]
    _ = (T.homologyπ n ≫ eH₀.hom) ≫ rH.hom ≫ eH₁.inv :=
      congrArg (fun z => z ≫ rH.hom ≫ eH₁.inv) h₃.symm
    _ = _ := by simp only [Category.assoc]


/-- Positive-tail cycle comparisons are natural under actual chain maps. -/
theorem positiveTailCyclesIso_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L)
    (hK : K.d 1 0 = 0) (hL : L.d 1 0 = 0) (n : ℕ) :
    HomologicalComplex.cyclesMap (positiveTailMap f) n ≫ (positiveTailCyclesIso L hL n).hom =
      (positiveTailCyclesIso K hK n).hom ≫ HomologicalComplex.cyclesMap f (n + 1) := by
  apply (cancel_mono (L.iCycles (n + 1))).mp
  have hl := (Category.assoc _ _ _).trans
    ((congrArg (fun z => HomologicalComplex.cyclesMap (positiveTailMap f) n ≫ z)
      (positiveTailCyclesIso_i L hL n)).trans
        (HomologicalComplex.cyclesMap_i (positiveTailMap f) n))
  have hr := (Category.assoc _ _ _).trans
    ((congrArg (fun z => (positiveTailCyclesIso K hK n).hom ≫ z)
      (HomologicalComplex.cyclesMap_i f (n + 1))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ f.f (n + 1)) (positiveTailCyclesIso_i K hK n))))
  exact hl.trans hr.symm


/-- Positive-tail homology comparisons are natural under actual chain maps. -/
theorem positiveTailHomologyIso_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L)
    (hK : K.d 1 0 = 0) (hL : L.d 1 0 = 0) (n : ℕ) :
    HomologicalComplex.homologyMap (positiveTailMap f) n ≫ (positiveTailHomologyIso L hL n).hom =
      (positiveTailHomologyIso K hK n).hom ≫ HomologicalComplex.homologyMap f (n + 1) := by
  apply (cancel_epi ((positiveTail K).homologyπ n)).mp
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
    ← positiveTailHomologyIso_π, ← Category.assoc, positiveTailCyclesIso_naturality,
    Category.assoc, ← HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, positiveTailHomologyIso_π, Category.assoc]

end

end ChainComplex

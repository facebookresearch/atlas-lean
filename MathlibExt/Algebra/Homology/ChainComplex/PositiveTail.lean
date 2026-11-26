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
# Positive tails and shifted homology

For a category C with zero morphisms, the positive tail T(K) of a nonnegative chain complex has
T(K)_n = K_{n+1} and differential d_K,n+2,n+1. Chain maps restrict to their components one
degree higher. In an abelian category, if d_K,1,0 = 0, there are natural isomorphisms Z_n(T(K))
≅ Z_{n+1}(K) and H_n(T(K)) ≅ H_{n+1}(K). At n = 0 both homology objects are the cokernel of
d_K,2,1; the isomorphisms commute with cycle inclusions and homology projections.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- Let C be a category with zero morphisms and K a natural-number-indexed chain complex. Its
positive tail T(K) has degree-n term K_{n+1} and differential T(K)_{n+1} → T(K)_n equal to
d_K,n+2,n+1. This construction imposes no condition on d_K,1,0. -/
def positiveTail (K : ChainComplex C ℕ) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => K.X (n + 1))
    (fun n => K.d (n + 2) (n + 1)) (fun _ => by simp)

@[simp]
theorem positiveTail_X (K : ChainComplex C ℕ) (n : ℕ) : (positiveTail K).X n = K.X (n + 1) := rfl

@[simp]
theorem positiveTail_d_succ (K : ChainComplex C ℕ) (n : ℕ) :
    (positiveTail K).d (n + 1) n = K.d (n + 2) (n + 1) := by
  simp only [positiveTail, ChainComplex.of_d]

/-- Let C be a category with zero morphisms and f : K → L a map of nonnegative chain complexes. The
positive-tail map T(f) : T(K) → T(L) has degree-n component f_{n+1}; it respects the tail
differentials and is functorial in f. -/
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

/-- Let C be abelian, K a nonnegative chain complex and n a natural number. The short complex
T(K)_{n+2} → T(K)_{n+1} → T(K)_n is canonically isomorphic to K_{n+3} → K_{n+2} → K_{n+1}, with
identity reindexing components. -/
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

/-- Let C be abelian and K a nonnegative chain complex. For the degree-zero short complex T(K)₁ →
T(K)₀ → T(K)₀, whose second map is zero, the chosen homology data have cycles T(K)₀ = K₁ and
homology coker(d_K,2,1), with the identity cycle inclusion and the cokernel projection. -/
def positiveTailZeroData (K : ChainComplex C ℕ) :
    ((positiveTail K).sc' 1 0 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofHasCokernel _ (by
    change (positiveTail K).d 0 0 = 0
    exact (positiveTail K).shape 0 0 (by decide))

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
The short complex K₂ → K₁ → K₀ has cycles K₁ and homology coker(d_K,2,1), with identity cycle
inclusion and the cokernel projection as its homology data. -/
def originalOneData (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    (K.sc' 2 1 0).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofHasCokernel _ hK

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
The homology objects in positiveTailZeroData K and originalOneData K are canonically isomorphic
via the identical incoming map d_K,2,1 : K₂ → K₁. -/
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

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For each natural number n, the cycles of T(K)_{n+1} → T(K)_n → T(K)_{n−1} are isomorphic to the
cycles of K_{n+2} → K_{n+1} → K_n. Here n−1 is natural-number subtraction; at n = 0 the
vanishing hypothesis identifies both cycle objects with K₁. -/
def positiveTailExplicitCyclesIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) :
    ∀ n : ℕ, ((positiveTail K).sc' (n + 1) n (n - 1)).cycles ≅
      (K.sc' (n + 2) (n + 1) n).cycles
  | 0 => (positiveTailZeroData K).cyclesIso ≪≫ (originalOneData K hK).cyclesIso.symm
  | n + 1 => by
      exact ShortComplex.cyclesMapIso (positiveTailRowIso K n)

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For every natural number n, the homology of T(K)_{n+1} → T(K)_n → T(K)_{n−1} is isomorphic to
that of K_{n+2} → K_{n+1} → K_n. In degree zero this is the comparison of their cokernels of
d_K,2,1. -/
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

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For every natural number n, positiveTailCyclesIso gives the canonical isomorphism Z_n(T(K)) ≅
Z_{n+1}(K). -/
def positiveTailCyclesIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTail K).cycles n ≅ K.cycles (n + 1) :=
  (positiveTail K).cyclesIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    positiveTailExplicitCyclesIso K hK n ≪≫
      (K.cyclesIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).symm

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For every natural number n, positiveTailHomologyIso gives the canonical isomorphism H_n(T(K)) ≅
H_{n+1}(K). -/
def positiveTailHomologyIso (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTail K).homology n ≅ K.homology (n + 1) :=
  (positiveTail K).homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp) ≪≫
    positiveTailExplicitHomologyIso K hK n ≪≫
      (K.homologyIsoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc]) (by simp)).symm

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For n ∈ ℕ and e_Z : Z_n(T(K)) ≅ Z_{n+1}(K), the cycle inclusions satisfy e_Z.hom ≫ i_Z,K,n+1 =
i_Z,T(K),n as maps to K_{n+1}. -/
theorem positiveTailCyclesIso_i (K : ChainComplex C ℕ) (hK : K.d 1 0 = 0) (n : ℕ) :
    (positiveTailCyclesIso K hK n).hom ≫ K.iCycles (n + 1) = (positiveTail K).iCycles n := by
  simp only [positiveTailCyclesIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [HomologicalComplex.cyclesIsoSc'_inv_iCycles, positiveTailExplicitCyclesIso_i]
  exact HomologicalComplex.cyclesIsoSc'_hom_iCycles _ _ _ _ _ _

/-- Let C be an abelian category and K a natural-number-indexed chain complex in C with d_K,1,0 = 0.
For n ∈ ℕ, let e_Z and e_H be the tail cycle and homology isomorphisms. Their projections
satisfy e_Z.hom ≫ π_K,n+1 = π_T(K),n ≫ e_H.hom. -/
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


/-- Let C be abelian, f : K → L a map of nonnegative chain complexes, and assume d_K,1,0 = d_L,1,0 =
0. For n ∈ ℕ, the cycle isomorphisms satisfy Z_n(T(f)) ≫ e_Z,L,n = e_Z,K,n ≫ Z_{n+1}(f). -/
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


/-- Let C be abelian, f : K → L a map of nonnegative chain complexes, and assume d_K,1,0 = d_L,1,0 =
0. For n ∈ ℕ, the homology isomorphisms satisfy H_n(T(f)) ≫ e_H,L,n = e_H,K,n ≫ H_{n+1}(f). -/
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

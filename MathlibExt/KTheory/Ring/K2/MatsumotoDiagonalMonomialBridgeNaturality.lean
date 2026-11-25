/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.MatsumotoDiagonalMonomialBridge

/-!
# Naturality of diagonal and monomial extension bridges

Constructs the maps induced by field homomorphisms on diagonal central
extensions and their monomial realizations. Proves that the inclusion bridges,
projection and central coefficient maps, and torus elements commute with these
field maps.
-/

@[expose] public section

open Matrix

namespace MatsumotoDiagonalMonomialBridgeNaturality

universe u v w

variable {F : Type u} {K : Type v} {L : Type w} [Field F] [Field K]
  [Field L]

section DiagMap

/-- Pointwise `Units.map` on determinant-one diagonal torus. -/
def DiagMap (f : F →+* K) (n : ℕ) :
    MatsumotoDiagonalExtension.Diag F n →*
      MatsumotoDiagonalExtension.Diag K n where
  toFun u :=
    ⟨fun i => Units.map f.toMonoidHom (u.val i), by
      have h_prod := MatsumotoDiagonalExtension.Diag.prod_eq_one F n u
      have h_map :
          ∏ i : Fin n, Units.map f.toMonoidHom (u.val i) =
            Units.map f.toMonoidHom (∏ i : Fin n, u.val i) := by
        rw [← map_prod (Units.map f.toMonoidHom) (fun i => u.val i)
          Finset.univ]
      have h_one : ∏ i : Fin n, Units.map f.toMonoidHom (u.val i) = 1 := by
        rw [h_map, h_prod, map_one]
      exact h_one⟩
  map_one' := by
    apply Subtype.ext
    funext i
    simp
  map_mul' x y := by
    apply Subtype.ext
    funext i
    simp

@[simp]
theorem DiagMap_apply (f : F →+* K) (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) (i : Fin n) :
    (DiagMap (F := F) (K := K) f n u).val i =
      Units.map f.toMonoidHom (u.val i) :=
  rfl

theorem DiagMap_coe (f : F →+* K) (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) :
    (DiagMap f n u).val =
      fun i => Units.map f.toMonoidHom (u.val i) :=
  rfl

theorem DiagMap_prod (f : F →+* K) (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) :
    ∏ i : Fin n, (DiagMap f n u).val i = 1 :=
  MatsumotoDiagonalExtension.Diag.prod_eq_one K n (DiagMap f n u)

@[simp]
theorem DiagMap_id (n : ℕ) :
    DiagMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (MatsumotoDiagonalExtension.Diag F n) := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  funext i
  simp [DiagMap]

theorem DiagMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    DiagMap (g.comp f) n =
      (DiagMap (F := K) (K := L) g n).comp
        (DiagMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  funext i
  have h1 : (g.comp f).toMonoidHom =
      g.toMonoidHom.comp f.toMonoidHom := rfl
  have h2 : Units.map (g.toMonoidHom.comp f.toMonoidHom) =
      (Units.map g.toMonoidHom).comp (Units.map f.toMonoidHom) :=
    Units.map_comp f.toMonoidHom g.toMonoidHom
  calc Units.map (g.comp f).toMonoidHom (u.val i)
      = Units.map (g.toMonoidHom.comp f.toMonoidHom) (u.val i) := by
        rw [h1]
    _ = ((Units.map g.toMonoidHom).comp
          (Units.map f.toMonoidHom)) (u.val i) := by
        rw [h2]
    _ = Units.map g.toMonoidHom
          (Units.map f.toMonoidHom (u.val i)) := rfl

theorem DiagMap_unitsTupleMap (f : F →+* K) (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) :
    MatsumotoPermutationAction.unitsTupleMap f n (u.val) =
      (DiagMap f n u).val := by
  funext i
  simp [MatsumotoPermutationAction.unitsTupleMap, DiagMap]

theorem DiagMap_d_ij (f : F →+* K) (n : ℕ) {i j : Fin n} (hij : i ≠ j)
    (u : Fˣ) :
    DiagMap f n (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
      MatsumotoDiagonalExtension.d_ij K n i j hij
        (Units.map f.toMonoidHom u) := by
  apply Subtype.ext
  funext k
  simp only [DiagMap_apply, MatsumotoDiagonalExtension.d_ij_val]
  by_cases hk1 : k = i
  · simp [hk1]
  · by_cases hk2 : k = j
    · simp [hk2, hij.symm, map_inv]
    · simp [hk1, hk2]

end DiagMap

section DiagMonomialNaturality

theorem diagMonomialHom_naturality (f : F →+* K) (n : ℕ) :
    (MatsumotoMonomialExtension.MMap (F := F) (K := K) f n).comp
        (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n) =
      (MatsumotoDiagonalMonomialBridge.diagMonomialHom K n).comp
        (DiagMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro u
  apply Subtype.ext
  simp only [MonoidHom.comp_apply]
  have h_coe :
      (MatsumotoMonomialExtension.MMap f n
          (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n u) :
        PermutationBilinearCocycle.MonomialBase Kˣ (Fin n)) =
        PermutationBilinearCocycle.monomialBaseHom
          (Units.map f.toMonoidHom)
          (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n u :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) := by
    exact MatsumotoMonomialExtension.coe_MMap f n
      (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n u)
  rw [h_coe]
  have h_left :
      (MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (DiagMap f n u) :
        PermutationBilinearCocycle.MonomialBase Kˣ (Fin n)) =
        ⟨fun i => Units.map f.toMonoidHom (u.val i), 1⟩ := by
    simp [MatsumotoDiagonalMonomialBridge.diagMonomialHom,
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase, DiagMap]
  have h_right :
      PermutationBilinearCocycle.monomialBaseHom (Units.map f.toMonoidHom)
          (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n u :
            PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) =
        ⟨fun i => Units.map f.toMonoidHom (u.val i), 1⟩ := by
    rw [MatsumotoDiagonalMonomialBridge.diagMonomialHom_coe]
    apply SemidirectProduct.ext
    · simp only [PermutationBilinearCocycle.monomialBaseHom_left,
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase]
      funext i
      simp only [PermutationBilinearCocycle.mapTupleHom_apply,
        PermutationBilinearCocycle.mapTuple_apply]
    · simp only [PermutationBilinearCocycle.monomialBaseHom_right]
      rfl
  rw [h_right, h_left]

theorem diagMonomialHom_naturality_apply (f : F →+* K) (n : ℕ)
    (u : MatsumotoDiagonalExtension.Diag F n) :
    MatsumotoMonomialExtension.MMap f n
        (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n u) =
      MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
        (DiagMap f n u) :=
  DFunLike.congr_fun (diagMonomialHom_naturality (F := F) (K := K) f n) u

end DiagMonomialNaturality

section HMapDef

/-- Compatibility for `HMap` via `alphaAddAll_naturality`. -/
noncomputable def HCompatibleMap (f : F →+* K) (n : ℕ) :
    NormalizedCocycleExtension.CompatibleMap
      (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle (F := F) (n := n))
      (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle (F := K) (n := n)) where
  f := DiagMap (F := F) (K := K) f n
  g := MilnorK.mapMultiplicative f 2
  q _ := 1
  q_one := rfl
  compat x y := by
    simp only [mul_one, one_mul]
    have h_alpha :
        MilnorK.mapMultiplicative f 2
            (MatsumotoDiagonalExtension.alpha F n x y) =
          MatsumotoDiagonalExtension.alpha K n
            (DiagMap f n x) (DiagMap f n y) := by
      unfold MatsumotoDiagonalExtension.alpha
      rw [MilnorK.mapMultiplicative_ofAdd_eq_map]
      have h_eq :
          MatsumotoDiagonalExtension.alphaAdd F n x y =
            MatsumotoDiagonalExtension.alphaAddAll F n
              (x.val) (y.val) :=
        MatsumotoDiagonalExtension.alphaAdd_eq_alphaAddAll F n x y
      rw [h_eq]
      have h_nat :=
        MatsumotoPermutationAction.alphaAddAll_naturality (F := F) (K := K)
          f n (x.val) (y.val)
      have h_units :
          MatsumotoPermutationAction.unitsTupleMap f n (x.val) =
            (DiagMap f n x).val :=
        (DiagMap_unitsTupleMap (F := F) (K := K) f n x).symm
      have h_units2 :
          MatsumotoPermutationAction.unitsTupleMap f n (y.val) =
            (DiagMap f n y).val :=
        (DiagMap_unitsTupleMap (F := F) (K := K) f n y).symm
      have h_calc :
          MilnorK.map f 2
              (MatsumotoDiagonalExtension.alphaAddAll F n
                (x.val) (y.val)) =
            MatsumotoDiagonalExtension.alphaAddAll K n
              ((DiagMap f n x).val) ((DiagMap f n y).val) := by
        calc MilnorK.map f 2
                (MatsumotoDiagonalExtension.alphaAddAll F n
                  (x.val) (y.val))
            = MatsumotoDiagonalExtension.alphaAddAll K n
                (MatsumotoPermutationAction.unitsTupleMap f n (x.val))
                (MatsumotoPermutationAction.unitsTupleMap f n (y.val)) :=
              h_nat
          _ = MatsumotoDiagonalExtension.alphaAddAll K n
                ((DiagMap f n x).val) ((DiagMap f n y).val) := by
              rw [← h_units, ← h_units2]
      have h_final :
          Multiplicative.ofAdd
              (MilnorK.map f 2
                (MatsumotoDiagonalExtension.alphaAddAll F n
                  (x.val) (y.val))) =
            Multiplicative.ofAdd
              (MatsumotoDiagonalExtension.alphaAdd K n
                (DiagMap f n x) (DiagMap f n y)) := by
        rw [h_calc, ←
          MatsumotoDiagonalExtension.alphaAdd_eq_alphaAddAll K n
            (DiagMap f n x) (DiagMap f n y)]
      exact h_final
    have h_eq :
        MilnorK.mapMultiplicative f 2
            ((MatsumotoDiagonalExtension.matsumotoDiagonalCocycle
                (F := F) (n := n)).cocycle x y) =
          (MatsumotoDiagonalExtension.matsumotoDiagonalCocycle
              (F := K) (n := n)).cocycle
            (DiagMap f n x) (DiagMap f n y) := by
      simpa using h_alpha
    rw [h_eq]

/-- Field-functorial lift `H F n →* H K n`. -/
noncomputable def HMap (f : F →+* K) (n : ℕ) :
    MatsumotoDiagonalExtension.H F n →*
      MatsumotoDiagonalExtension.H K n :=
  (HCompatibleMap (F := F) (K := K) f n).toHom

@[simp]
theorem HMap_base (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    (HMap (F := F) (K := K) f n h).base =
      DiagMap f n h.base :=
  rfl

theorem HMap_coeff (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    (HMap f n h).coeff =
      MilnorK.mapMultiplicative f 2 h.coeff := by
  change ((HCompatibleMap (F := F) (K := K) f n).toHom h).coeff =
      MilnorK.mapMultiplicative f 2 h.coeff
  simp [HCompatibleMap]

theorem HMap_inl (f : F →+* K) (n : ℕ)
    (c : Multiplicative (MilnorK F 2)) :
    HMap (F := F) (K := K) f n
        (MatsumotoDiagonalExtension.inlHom F n c) =
      MatsumotoDiagonalExtension.inlHom K n
        (MilnorK.mapMultiplicative f 2 c) := by
  apply NormalizedCocycleExtension.Extension.ext
  · simp [HMap_base, MatsumotoDiagonalExtension.inlHom]
  · simp [HMap_coeff, MatsumotoDiagonalExtension.inlHom]

theorem HMap_proj (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoDiagonalExtension.projHom K n (HMap f n h) =
      DiagMap f n (MatsumotoDiagonalExtension.projHom F n h) :=
  rfl

theorem HMap_comp_inl (f : F →+* K) (n : ℕ) :
    (HMap (F := F) (K := K) f n).comp
        (MatsumotoDiagonalExtension.inlHom F n) =
      (MatsumotoDiagonalExtension.inlHom K n).comp
        (MilnorK.mapMultiplicative f 2) := by
  apply MonoidHom.ext
  intro c
  exact HMap_inl (F := F) (K := K) f n c

theorem HMap_comp_proj (f : F →+* K) (n : ℕ) :
    (MatsumotoDiagonalExtension.projHom K n).comp
        (HMap (F := F) (K := K) f n) =
      (DiagMap f n).comp (MatsumotoDiagonalExtension.projHom F n) := by
  apply MonoidHom.ext
  intro h
  rfl

theorem HMap_id (n : ℕ) :
    HMap (F := F) (K := F) (RingHom.id F) n =
      MonoidHom.id (MatsumotoDiagonalExtension.H F n) := by
  apply MonoidHom.ext
  intro h
  apply NormalizedCocycleExtension.Extension.ext
  · simp [HMap_base, DiagMap_id]
  · simp [HMap_coeff, MilnorK.mapMultiplicative_id]

theorem HMap_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    HMap (g.comp f) n =
      (HMap (F := K) (K := L) g n).comp
        (HMap (F := F) (K := K) f n) := by
  apply MonoidHom.ext
  intro h
  apply NormalizedCocycleExtension.Extension.ext
  · simp [HMap_base, DiagMap_comp]
  · simp [HMap_coeff, MilnorK.mapMultiplicative_comp]

end HMapDef

section HToHAllNaturality

theorem HToHAll_naturality (f : F →+* K) (n : ℕ) :
    (MatsumotoPermutationAction.HAllMap f n).comp
        (MatsumotoDiagonalMonomialBridge.HToHAll F n) =
      (MatsumotoDiagonalMonomialBridge.HToHAll K n).comp
        (HMap f n) := by
  apply MonoidHom.ext
  intro h
  apply NormalizedCocycleExtension.Extension.ext
  · simp [MatsumotoDiagonalMonomialBridge.HToHAll_base, HMap_base,
      MatsumotoPermutationAction.HAllMap_base, DiagMap_unitsTupleMap]
  · simp [MatsumotoDiagonalMonomialBridge.HToHAll_coeff, HMap_coeff,
      MatsumotoPermutationAction.HAllMap_coeff]

theorem HToHAll_naturality_apply (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoPermutationAction.HAllMap f n
        (MatsumotoDiagonalMonomialBridge.HToHAll F n h) =
      MatsumotoDiagonalMonomialBridge.HToHAll K n (HMap f n h) :=
  DFunLike.congr_fun (HToHAll_naturality (F := F) (K := K) f n) h

end HToHAllNaturality

section HToHMNaturality

theorem HToHM_naturality (f : F →+* K) (n : ℕ) :
    (MatsumotoMonomialExtension.HMMap f n).comp
        (MatsumotoDiagonalMonomialBridge.HToHM F n) =
      (MatsumotoDiagonalMonomialBridge.HToHM K n).comp
        (HMap f n) := by
  apply MonoidHom.ext
  intro h
  apply Subtype.ext
  apply Prod.ext
  · change MatsumotoMonomialExtension.ambientLiftHom K n
          (MatsumotoMonomialExtension.HMMap f n
            (MatsumotoDiagonalMonomialBridge.HToHM F n h)) =
        MatsumotoMonomialExtension.ambientLiftHom K n
          (MatsumotoDiagonalMonomialBridge.HToHM K n (HMap f n h))
    rw [MatsumotoMonomialExtension.HMMap_fst,
      MatsumotoDiagonalMonomialBridge.HToHM_ambientLiftHom,
      MatsumotoDiagonalMonomialBridge.HToHM_ambientLiftHom]
    simp only [MatsumotoDiagonalMonomialBridge.ambientLiftMapH,
      MonoidHom.comp_apply]
    have h_lift :
        (MatsumotoMonomialExtension.ambientMonomialLiftMap f n).comp
            (MatsumotoDiagonalMonomialBridge.HAllToMonomialLift F n) =
          (MatsumotoDiagonalMonomialBridge.HAllToMonomialLift K n).comp
            (MatsumotoPermutationAction.HAllMap f n) := by
      apply MonoidHom.ext
      intro x
      apply SemidirectProduct.ext
      · rfl
      · rfl
    have h1 := DFunLike.congr_fun h_lift
      (MatsumotoDiagonalMonomialBridge.HToHAll F n h)
    simp only [MonoidHom.comp_apply] at h1
    rw [h1, HToHAll_naturality_apply]
  · change MatsumotoMonomialExtension.projHom K n
          (MatsumotoMonomialExtension.HMMap f n
            (MatsumotoDiagonalMonomialBridge.HToHM F n h)) =
        MatsumotoMonomialExtension.projHom K n
          (MatsumotoDiagonalMonomialBridge.HToHM K n (HMap f n h))
    rw [MatsumotoMonomialExtension.HMMap_snd,
      MatsumotoDiagonalMonomialBridge.HToHM_projHom,
      MatsumotoDiagonalMonomialBridge.HToHM_projHom]
    simp only [MatsumotoDiagonalMonomialBridge.projMapH,
      MonoidHom.comp_apply]
    have h_proj :
        MatsumotoDiagonalExtension.projHom K n (HMap f n h) =
          DiagMap f n (MatsumotoDiagonalExtension.projHom F n h) := rfl
    rw [h_proj, ← diagMonomialHom_naturality_apply]

theorem HToHM_naturality_apply (f : F →+* K) (n : ℕ)
    (h : MatsumotoDiagonalExtension.H F n) :
    MatsumotoMonomialExtension.HMMap f n
        (MatsumotoDiagonalMonomialBridge.HToHM F n h) =
      MatsumotoDiagonalMonomialBridge.HToHM K n (HMap f n h) :=
  DFunLike.congr_fun (HToHM_naturality (F := F) (K := K) f n) h

end HToHMNaturality

section HijNaturality

theorem h_ij_naturality (f : F →+* K) (n : ℕ) {i j : Fin n}
    (hij : i ≠ j) (u : Fˣ) :
    HMap f n (MatsumotoDiagonalExtension.h_ij F n i j hij u) =
      MatsumotoDiagonalExtension.h_ij K n i j hij
        (Units.map f.toMonoidHom u) := by
  have h_base :
      DiagMap f n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u).base =
        (MatsumotoDiagonalExtension.h_ij K n i j hij
            (Units.map f.toMonoidHom u)).base := by
    simp [MatsumotoDiagonalExtension.h_ij_diag, DiagMap_d_ij]
  have h_coeff :
      MilnorK.mapMultiplicative f 2
          (MatsumotoDiagonalExtension.h_ij F n i j hij u).coeff =
        (MatsumotoDiagonalExtension.h_ij K n i j hij
            (Units.map f.toMonoidHom u)).coeff := by
    by_cases h_lt : i < j
    · have h1 :
          (MatsumotoDiagonalExtension.h_ij F n i j hij u).coeff = 1 := by
        exact MatsumotoDiagonalExtension.h_ij_coeff_lt F n hij u h_lt
      have h2 :
          (MatsumotoDiagonalExtension.h_ij K n i j hij
              (Units.map f.toMonoidHom u)).coeff = 1 := by
        exact MatsumotoDiagonalExtension.h_ij_coeff_lt K n hij
          (Units.map f.toMonoidHom u) h_lt
      rw [h1, h2, map_one]
    · have h1 :
          (MatsumotoDiagonalExtension.h_ij F n i j hij u).coeff =
            Multiplicative.ofAdd (MilnorK.k2Symbol F u u) := by
        exact MatsumotoDiagonalExtension.h_ij_coeff_gt F n hij u h_lt
      have h2 :
          (MatsumotoDiagonalExtension.h_ij K n i j hij
              (Units.map f.toMonoidHom u)).coeff =
            Multiplicative.ofAdd
              (MilnorK.k2Symbol K (Units.map f.toMonoidHom u)
                (Units.map f.toMonoidHom u)) := by
        exact MatsumotoDiagonalExtension.h_ij_coeff_gt K n hij
          (Units.map f.toMonoidHom u) h_lt
      rw [h1, h2, MilnorK.mapMultiplicative_ofAdd_eq_map,
        MilnorK.map_k2Symbol]
  apply NormalizedCocycleExtension.Extension.ext
  · exact h_base
  · have h_map := HMap_coeff (F := F) (K := K) f n
        (MatsumotoDiagonalExtension.h_ij F n i j hij u)
    rw [h_map, h_coeff]

theorem h_ij_HM_naturality (f : F →+* K) (n : ℕ) {i j : Fin n}
    (hij : i ≠ j) (u : Fˣ) :
    MatsumotoMonomialExtension.HMMap f n
        (MatsumotoDiagonalMonomialBridge.HToHM F n
          (MatsumotoDiagonalExtension.h_ij F n i j hij u)) =
      MatsumotoDiagonalMonomialBridge.HToHM K n
        (MatsumotoDiagonalExtension.h_ij K n i j hij
          (Units.map f.toMonoidHom u)) := by
  rw [← h_ij_naturality (F := F) (K := K) f n hij u,
    ← HToHM_naturality_apply (F := F) (K := K) f n]

theorem h_ij_HM_proj_naturality (f : F →+* K) (n : ℕ) {i j : Fin n}
    (hij : i ≠ j) (u : Fˣ) :
    MatsumotoMonomialExtension.projHom K n
        (MatsumotoDiagonalMonomialBridge.HToHM K n
          (MatsumotoDiagonalExtension.h_ij K n i j hij
            (Units.map f.toMonoidHom u))) =
      MatsumotoMonomialExtension.MMap f n
        (MatsumotoMonomialExtension.projHom F n
          (MatsumotoDiagonalMonomialBridge.HToHM F n
            (MatsumotoDiagonalExtension.h_ij F n i j hij u))) := by
  have h_diag :
      DiagMap f n (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
        MatsumotoDiagonalExtension.d_ij K n i j hij
          (Units.map f.toMonoidHom u) :=
    DiagMap_d_ij f n hij u
  have h_torus_eq :
      MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (MatsumotoDiagonalExtension.d_ij K n i j hij
            (Units.map f.toMonoidHom u)) =
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij
          (Units.map f.toMonoidHom u) := by
    apply Subtype.ext
    have h_base :
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase K n
            (MatsumotoDiagonalExtension.d_ij K n i j hij
              (Units.map f.toMonoidHom u)) =
          Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij
            (Units.map f.toMonoidHom u) :=
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
        K n hij (Units.map f.toMonoidHom u)
    calc (MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
            (MatsumotoDiagonalExtension.d_ij K n i j hij
              (Units.map f.toMonoidHom u)) :
          PermutationBilinearCocycle.MonomialBase Kˣ (Fin n))
        = MatsumotoDiagonalMonomialBridge.diagToMonomialBase K n
            (MatsumotoDiagonalExtension.d_ij K n i j hij
              (Units.map f.toMonoidHom u)) := rfl
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij
            (Units.map f.toMonoidHom u) := h_base
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij
            (Units.map f.toMonoidHom u) :
          PermutationBilinearCocycle.MonomialBase Kˣ (Fin n)) := rfl
  have h_torus_eq_F :
      MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
          (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
        Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u := by
    apply Subtype.ext
    have h_base :
        MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u) =
          Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u :=
      MatsumotoDiagonalMonomialBridge.diagToMonomialBase_eq_torusWeight
        F n hij u
    calc (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u) :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n))
        = MatsumotoDiagonalMonomialBridge.diagToMonomialBase F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u) := rfl
      _ = Matrix.GeneralLinearGroup.torusMonomialBaseUnit i j hij u := h_base
      _ = (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u :
          PermutationBilinearCocycle.MonomialBase Fˣ (Fin n)) := rfl
  calc MatsumotoMonomialExtension.projHom K n
          (MatsumotoDiagonalMonomialBridge.HToHM K n
            (MatsumotoDiagonalExtension.h_ij K n i j hij
              (Units.map f.toMonoidHom u)))
      = MatsumotoDiagonalMonomialBridge.projMapH K n
          (MatsumotoDiagonalExtension.h_ij K n i j hij
            (Units.map f.toMonoidHom u)) := by
        exact MatsumotoDiagonalMonomialBridge.HToHM_projHom K n
          (MatsumotoDiagonalExtension.h_ij K n i j hij
            (Units.map f.toMonoidHom u))
    _ = MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (MatsumotoDiagonalExtension.d_ij K n i j hij
            (Units.map f.toMonoidHom u)) := by
        have h1 :
            MatsumotoDiagonalMonomialBridge.projMapH K n
                (MatsumotoDiagonalExtension.h_ij K n i j hij
                  (Units.map f.toMonoidHom u)) =
              MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
                (MatsumotoDiagonalExtension.projHom K n
                  (MatsumotoDiagonalExtension.h_ij K n i j hij
                    (Units.map f.toMonoidHom u))) := rfl
        have h2 :
            MatsumotoDiagonalExtension.projHom K n
                (MatsumotoDiagonalExtension.h_ij K n i j hij
                  (Units.map f.toMonoidHom u)) =
              MatsumotoDiagonalExtension.d_ij K n i j hij
                (Units.map f.toMonoidHom u) := by
          change (MatsumotoDiagonalExtension.h_ij K n i j hij
              (Units.map f.toMonoidHom u)).base =
            MatsumotoDiagonalExtension.d_ij K n i j hij
              (Units.map f.toMonoidHom u)
          exact MatsumotoDiagonalExtension.h_ij_diag K n i j hij
            (Units.map f.toMonoidHom u)
        rw [h1, h2]
    _ = MatsumotoDiagonalMonomialBridge.diagMonomialHom K n
          (DiagMap f n (MatsumotoDiagonalExtension.d_ij F n i j hij u)) := by
        rw [← h_diag]
    _ = MatsumotoMonomialExtension.MMap f n
          (MatsumotoDiagonalMonomialBridge.diagMonomialHom F n
            (MatsumotoDiagonalExtension.d_ij F n i j hij u)) := by
        rw [← diagMonomialHom_naturality_apply]
    _ = MatsumotoMonomialExtension.MMap f n
          (Matrix.GeneralLinearGroup.torusMonomialSLUnit i j hij u) := by
        rw [h_torus_eq_F]
    _ = MatsumotoMonomialExtension.MMap f n
          (MatsumotoMonomialExtension.projHom F n
            (MatsumotoDiagonalMonomialBridge.HToHM F n
              (MatsumotoDiagonalExtension.h_ij F n i j hij u))) := by
        rw [MatsumotoDiagonalMonomialBridge.HToHM_h_ij_proj]

end HijNaturality

end MatsumotoDiagonalMonomialBridgeNaturality

end

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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.CanonicalPivot
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IsolatedCoordinate
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.Data.Fintype.Card

/-!
# Canonical pivot reduction to an isolated diagonal block

For `g : GL ι K` over a division ring, the canonical pivot clearing produces a matrix
whose column `c` and, when `c` is least, row `pivotRow g c` are isolated.
Swapping rows `pivotRow g c ↔ c` turns the off-diagonal pivot into an isolated
diagonal coordinate at `c`. Deleting `c` yields the smaller `GL (DeletedIndex ι c) K`
block for recursive Bruhat extraction.

API:
* `canonicalPivotUnitAt` / `alignedPivotUnitAt` / `reducedPivotBlockAt`
* least-index variants `canonicalPivotUnit` / `alignedPivotUnit` / `reducedPivotBlock`
* cardinal decrease `Fintype.card (DeletedIndex ι c) = Fintype.card ι - 1`
* naturality under arbitrary division-ring homs `f : K →+* L`
* optional factorisation recovering `g`

Uses `canonicalPivotClearedAt_*` isolation lemmas and `Matrix.swap` row-action lemmas
without expanding permutation matrices.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

open Matrix

universe uι uK vK

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] [LinearOrder ι]
variable {K : Type uK} [DivisionRing K]

/-! ## Canonical pivot unit -/

/-- `rowClear * g * columnClear` as a `GL` element. -/
noncomputable def canonicalPivotUnitAt (g : GL ι K) (c : ι) : GL ι K :=
  let M := (↑g : Matrix ι ι K)
  let r := pivotRow g c
  let hp := pivotRow_ne_zero g c
  rowClear M r c hp * g * columnClear M r c hp

theorem coe_canonicalPivotUnitAt (g : GL ι K) (c : ι) :
    (↑(canonicalPivotUnitAt g c) : Matrix ι ι K) = canonicalPivotClearedAt g c :=
  rfl

/-! ## Swap alignment -/

/-- Row transposition `pivotRow g c ↔ c`. -/
noncomputable def pivotSwap (g : GL ι K) (c : ι) : Equiv.Perm ι :=
  Equiv.swap (pivotRow g c) c

/-- Permutation unit for `pivotSwap`. -/
noncomputable def pivotPermutation (g : GL ι K) (c : ι) : GL ι K :=
  permutationUnitsHom K ι (pivotSwap g c)

theorem pivotSwap_self_inv (g : GL ι K) (c : ι) :
    (pivotSwap g c)⁻¹ = pivotSwap g c := by
  unfold pivotSwap
  -- `Equiv.swap` is involutive: symm = itself, and Perm inverse = symm
  have h : (Equiv.swap (pivotRow g c) c).symm = Equiv.swap (pivotRow g c) c :=
    Equiv.symm_swap (pivotRow g c) c
  -- for Perm, inverse is symm
  calc (Equiv.swap (pivotRow g c) c : Equiv.Perm ι)⁻¹
      = (Equiv.swap (pivotRow g c) c).symm := rfl
    _ = Equiv.swap (pivotRow g c) c := h

theorem coe_pivotPermutation (g : GL ι K) (c : ι) :
    (↑(pivotPermutation g c) : Matrix ι ι K) = Matrix.swap K (pivotRow g c) c := by
  unfold pivotPermutation pivotSwap
  rw [coe_permutationUnitsHom]
  have h_inv : (Equiv.swap (pivotRow g c) c : Equiv.Perm ι)⁻¹ =
      Equiv.swap (pivotRow g c) c := by
    have h : (Equiv.swap (pivotRow g c) c).symm = Equiv.swap (pivotRow g c) c :=
      Equiv.symm_swap (pivotRow g c) c
    calc (Equiv.swap (pivotRow g c) c : Equiv.Perm ι)⁻¹
        = (Equiv.swap (pivotRow g c) c).symm := rfl
      _ = Equiv.swap (pivotRow g c) c := h
  rw [h_inv]
  rfl

/-- Swap-aligned pivot unit: permutation moves the isolated row to diagonal `c`. -/
noncomputable def alignedPivotUnitAt (g : GL ι K) (c : ι) : GL ι K :=
  pivotPermutation g c * canonicalPivotUnitAt g c

theorem coe_alignedPivotUnitAt (g : GL ι K) (c : ι) :
    (↑(alignedPivotUnitAt g c) : Matrix ι ι K) =
      Matrix.swap K (pivotRow g c) c * canonicalPivotClearedAt g c := by
  unfold alignedPivotUnitAt
  calc (↑(pivotPermutation g c * canonicalPivotUnitAt g c) : Matrix ι ι K)
      = (↑(pivotPermutation g c) : Matrix ι ι K) *
        (↑(canonicalPivotUnitAt g c) : Matrix ι ι K) := by
          rw [Units.val_mul]
    _ = Matrix.swap K (pivotRow g c) c * canonicalPivotClearedAt g c := by
          rw [coe_pivotPermutation, coe_canonicalPivotUnitAt]

/-! ## Isolated diagonal after swap -/

theorem alignedPivotIsolatedAt (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) :
    IsolatedCoordinate (alignedPivotUnitAt g c) c := by
  let pRow := pivotRow g c
  let Bmat : Matrix ι ι K := canonicalPivotClearedAt (K := K) g c
  have hA : (↑(alignedPivotUnitAt g c) : Matrix ι ι K) =
      Matrix.swap K pRow c * Bmat := coe_alignedPivotUnitAt g c
  have hBcol : ∀ i : ι, Bmat i c =
      if i = pRow then (↑g : Matrix ι ι K) pRow c else 0 :=
    fun i => canonicalPivotClearedAt_col_isolated g c i
  have hBrow : ∀ j : ι, Bmat pRow j =
      if j = c then (↑g : Matrix ι ι K) pRow c else 0 :=
    fun j => canonicalPivotClearedAt_row_isolated_of_isLeast g c hc j
  constructor
  · intro i hi
    have h_eq : (↑(alignedPivotUnitAt g c) : Matrix ι ι K) i c =
        (Matrix.swap K pRow c * Bmat) i c := by rw [hA]
    rw [h_eq]
    by_cases h_ir : i = pRow
    · have h_rc_ne : pRow ≠ c := by
        intro h_eq
        exact hi (h_ir.trans h_eq)
      have h_swap_left : (Matrix.swap K pRow c * Bmat) pRow c = Bmat c c := by
        have := Matrix.swap_mul_apply_left (R := K) pRow c c Bmat
        exact this
      have h_rw : (Matrix.swap K pRow c * Bmat) i c =
          (Matrix.swap K pRow c * Bmat) pRow c := by rw [h_ir]
      rw [h_rw, h_swap_left, hBcol c]
      simp [Ne.symm h_rc_ne]
    · have h_i_ne_r : i ≠ pRow := h_ir
      have h_i_ne_c : i ≠ c := hi
      have h_swap_ne : (Matrix.swap K pRow c * Bmat) i c = Bmat i c :=
        Matrix.swap_mul_of_ne h_i_ne_r h_i_ne_c Bmat
      rw [h_swap_ne, hBcol i]
      simp [h_i_ne_r]
  · intro j hj
    have h_eq : (↑(alignedPivotUnitAt g c) : Matrix ι ι K) c j =
        (Matrix.swap K pRow c * Bmat) c j := by rw [hA]
    rw [h_eq]
    have h_swap_right : (Matrix.swap K pRow c * Bmat) c j = Bmat pRow j := by
      have := Matrix.swap_mul_apply_right (R := K) pRow c j Bmat
      exact this
    rw [h_swap_right, hBrow j]
    simp [hj]

/-! ## Reduced block -/

/-- Deleting the isolated coordinate `c` after alignment. -/
noncomputable def reducedPivotBlockAt (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) :
    GL (DeletedIndex ι c) K :=
  deleteCoordinate (alignedPivotUnitAt g c) c (alignedPivotIsolatedAt g c hc)

theorem coe_reducedPivotBlockAt (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) :
    (↑(reducedPivotBlockAt g c hc) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) K) =
      (↑(alignedPivotUnitAt g c) : Matrix ι ι K).submatrix Subtype.val Subtype.val :=
  rfl

theorem coe_reducedPivotBlockAt_eq (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) :
    (↑(reducedPivotBlockAt g c hc) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) K) =
      (Matrix.swap K (pivotRow g c) c * canonicalPivotClearedAt g c).submatrix
        Subtype.val Subtype.val := by
  rw [coe_reducedPivotBlockAt, coe_alignedPivotUnitAt]

theorem coe_inv_reducedPivotBlockAt (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) :
    (↑(reducedPivotBlockAt g c hc)⁻¹ : Matrix (DeletedIndex ι c) (DeletedIndex ι c) K) =
      (↑(alignedPivotUnitAt g c)⁻¹ : Matrix ι ι K).submatrix Subtype.val Subtype.val :=
  rfl

/-! ## Least-index variants -/

section LeastIndex

variable [Nonempty ι]

/-- Canonical pivot clearing at `leastIndex`. -/
noncomputable def canonicalPivotUnit (g : GL ι K) : GL ι K :=
  canonicalPivotUnitAt g (leastIndex (ι := ι))

/-- Aligned version at `leastIndex`. -/
noncomputable def alignedPivotUnit (g : GL ι K) : GL ι K :=
  alignedPivotUnitAt g (leastIndex (ι := ι))

/-- Reduced block at `leastIndex`. -/
noncomputable def reducedPivotBlock (g : GL ι K) :
    GL (DeletedIndex ι (leastIndex (ι := ι))) K :=
  reducedPivotBlockAt g (leastIndex (ι := ι)) (leastIndex_isLeast (ι := ι))

theorem coe_canonicalPivotUnit (g : GL ι K) :
    (↑(canonicalPivotUnit g) : Matrix ι ι K) =
      canonicalPivotCleared (K := K) g := by
  unfold canonicalPivotUnit canonicalPivotCleared
  rfl

theorem coe_alignedPivotUnit (g : GL ι K) :
    (↑(alignedPivotUnit g) : Matrix ι ι K) =
      Matrix.swap K (pivotRow g (leastIndex (ι := ι))) (leastIndex (ι := ι)) *
        canonicalPivotCleared (K := K) g := by
  unfold alignedPivotUnit canonicalPivotCleared
  exact coe_alignedPivotUnitAt g (leastIndex (ι := ι))

theorem alignedPivotUnit_isolated (g : GL ι K) :
    IsolatedCoordinate (alignedPivotUnit g) (leastIndex (ι := ι)) :=
  alignedPivotIsolatedAt g (leastIndex (ι := ι)) (leastIndex_isLeast (ι := ι))

theorem coe_reducedPivotBlock (g : GL ι K) :
    (↑(reducedPivotBlock g) : Matrix (DeletedIndex ι (leastIndex (ι := ι)))
        (DeletedIndex ι (leastIndex (ι := ι))) K) =
      (↑(alignedPivotUnit g) : Matrix ι ι K).submatrix Subtype.val Subtype.val :=
  rfl

theorem coe_reducedPivotBlock_eq (g : GL ι K) :
    (↑(reducedPivotBlock g) : Matrix (DeletedIndex ι (leastIndex (ι := ι)))
        (DeletedIndex ι (leastIndex (ι := ι))) K) =
      (Matrix.swap K (pivotRow g (leastIndex (ι := ι))) (leastIndex (ι := ι)) *
        canonicalPivotCleared (K := K) g).submatrix Subtype.val Subtype.val := by
  rw [coe_reducedPivotBlock, coe_alignedPivotUnit]

end LeastIndex

/-! ## Cardinality decrease -/

omit [LinearOrder ι] in
theorem card_DeletedIndex (c : ι) :
    Fintype.card (DeletedIndex ι c) = Fintype.card ι - 1 := by
  have h_one : Fintype.card { x : ι // x = c } = 1 :=
    Fintype.card_subtype_eq c
  have h_compl : Fintype.card { x : ι // ¬(x = c) } =
      Fintype.card ι - Fintype.card { x : ι // x = c } :=
    Fintype.card_subtype_compl (fun x => x = c)
  calc Fintype.card (DeletedIndex ι c)
      = Fintype.card { x : ι // ¬(x = c) } := rfl
    _ = Fintype.card ι - Fintype.card { x : ι // x = c } := h_compl
    _ = Fintype.card ι - 1 := by rw [h_one]

omit [LinearOrder ι] in
theorem card_DeletedIndex_lt [Nonempty ι] (c : ι) :
    Fintype.card (DeletedIndex ι c) < Fintype.card ι := by
  have h_eq := card_DeletedIndex (ι := ι) c
  have h_pos : 0 < Fintype.card ι := Fintype.card_pos
  omega

/-! ## Naturality under division-ring homs -/

section Naturality

variable {L : Type vK} [DivisionRing L]
variable (f : K →+* L)

private theorem divRingHom_injective_of_div (f : K →+* L) : Function.Injective f := by
  intro a b hab
  by_contra hne
  have h_sub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h_map : f (a - b) = 0 := by
    rw [f.map_sub, hab, sub_self]
  have h_mul : f (a - b) * f (a - b)⁻¹ = 1 := by
    have h1 : (a - b) * (a - b)⁻¹ = 1 := mul_inv_cancel₀ h_sub
    calc f (a - b) * f (a - b)⁻¹
        = f ((a - b) * (a - b)⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  rw [h_map, zero_mul] at h_mul
  exact one_ne_zero h_mul.symm

private theorem divRingHom_map_ne_zero_of_div {a : K} (ha : a ≠ 0) (f : K →+* L) :
    f a ≠ 0 := by
  intro h0
  have h1 : f (a * a⁻¹) = f 1 := by rw [mul_inv_cancel₀ ha]
  have hmul : f a * f a⁻¹ = 1 := by
    calc f a * f a⁻¹ = f (a * a⁻¹) := by rw [← f.map_mul]
      _ = f 1 := by rw [h1]
      _ = 1 := f.map_one
  rw [h0, zero_mul] at hmul
  exact one_ne_zero hmul.symm

theorem pivotRow_mapRingHom_div (g : GL ι K) (c : ι) (f : K →+* L) :
    pivotRow (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c = pivotRow g c := by
  have hf : Function.Injective f := divRingHom_injective_of_div f
  exact pivotRow_mapRingHom (R := K) (S := L) f hf g c

theorem pivotSwap_mapRingHom_div (g : GL ι K) (c : ι) (f : K →+* L) :
    pivotSwap (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c = pivotSwap g c := by
  unfold pivotSwap
  rw [pivotRow_mapRingHom_div g c f]

theorem canonicalPivotUnitAt_mapRingHom (g : GL ι K) (c : ι) (f : K →+* L) :
    Matrix.GeneralLinearGroup.mapRingHom (n := ι) f (canonicalPivotUnitAt g c) =
      canonicalPivotUnitAt (Matrix.GeneralLinearGroup.mapRingHom (n := ι) f g) c := by
  apply Units.ext
  simp only [coe_mapRingHom]
  rw [coe_canonicalPivotUnitAt, coe_canonicalPivotUnitAt]
  exact canonicalPivotClearedAt_map f g c

theorem pivotPermutation_mapRingHom (g : GL ι K) (c : ι)
    (f : K →+* L) :
    mapRingHom (n := ι) f (pivotPermutation g c) =
      pivotPermutation (mapRingHom (n := ι) f g) c := by
  unfold pivotPermutation
  have h_swap_eq : pivotSwap (mapRingHom (n := ι) f g) c = pivotSwap g c :=
    pivotSwap_mapRingHom_div g c f
  calc mapRingHom (n := ι) f (permutationUnitsHom K ι (pivotSwap g c))
      = permutationUnitsHom L ι (pivotSwap g c) :=
          permutationUnitsHom_mapRingHom f (pivotSwap g c)
    _ = permutationUnitsHom L ι (pivotSwap (mapRingHom (n := ι) f g) c) := by
          rw [h_swap_eq]

theorem alignedPivotUnitAt_mapRingHom (g : GL ι K) (c : ι)
    (f : K →+* L) :
    mapRingHom (n := ι) f (alignedPivotUnitAt g c) =
      alignedPivotUnitAt (mapRingHom (n := ι) f g) c := by
  unfold alignedPivotUnitAt
  rw [map_mul]
  rw [pivotPermutation_mapRingHom g c f,
    canonicalPivotUnitAt_mapRingHom g c f]

omit [LinearOrder ι] in
private theorem deleteCoordinate_proof_irrel (g : GL ι K) (c : ι)
    (h1 h2 : IsolatedCoordinate g c) :
    deleteCoordinate g c h1 = deleteCoordinate g c h2 := by
  apply Units.ext
  rfl

theorem reducedPivotBlockAt_mapRingHom (g : GL ι K) (c : ι)
    (hc : IsLeast (Set.univ : Set ι) c) (f : K →+* L) :
    mapRingHom (n := DeletedIndex ι c) f (reducedPivotBlockAt g c hc) =
      reducedPivotBlockAt (mapRingHom (n := ι) f g) c hc := by
  unfold reducedPivotBlockAt
  have h_map_del :
      mapRingHom (n := DeletedIndex ι c) f
        (deleteCoordinate (alignedPivotUnitAt g c) c
          (alignedPivotIsolatedAt g c hc)) =
      deleteCoordinate (mapRingHom (n := ι) f (alignedPivotUnitAt g c)) c
        ((alignedPivotIsolatedAt g c hc).map f) := by
    rw [← mapRingHom_deleteCoordinate]
  calc mapRingHom (n := DeletedIndex ι c) f
          (deleteCoordinate (alignedPivotUnitAt g c) c
            (alignedPivotIsolatedAt g c hc))
      = deleteCoordinate (mapRingHom (n := ι) f (alignedPivotUnitAt g c)) c
          ((alignedPivotIsolatedAt g c hc).map f) := h_map_del
    _ = deleteCoordinate (alignedPivotUnitAt (mapRingHom (n := ι) f g) c) c
          (alignedPivotIsolatedAt (mapRingHom (n := ι) f g) c hc) := by
            have h_aligned_val :
                (↑(mapRingHom (n := ι) f (alignedPivotUnitAt g c)) :
                  Matrix ι ι L) =
                (↑(alignedPivotUnitAt (mapRingHom (n := ι) f g) c) :
                  Matrix ι ι L) := by
              rw [alignedPivotUnitAt_mapRingHom]
            apply Units.ext
            simp only [coe_deleteCoordinate]
            rw [h_aligned_val]

section Least

variable [Nonempty ι]

theorem canonicalPivotUnit_mapRingHom (g : GL ι K)
    (f : K →+* L) :
    mapRingHom (n := ι) f (canonicalPivotUnit g) =
      canonicalPivotUnit (mapRingHom (n := ι) f g) :=
  canonicalPivotUnitAt_mapRingHom g (leastIndex (ι := ι)) f

theorem alignedPivotUnit_mapRingHom (g : GL ι K)
    (f : K →+* L) :
    mapRingHom (n := ι) f (alignedPivotUnit g) =
      alignedPivotUnit (mapRingHom (n := ι) f g) :=
  alignedPivotUnitAt_mapRingHom g (leastIndex (ι := ι)) f

theorem reducedPivotBlock_mapRingHom (g : GL ι K)
    (f : K →+* L) :
    let c0 := leastIndex (ι := ι)
    mapRingHom (n := DeletedIndex ι c0) f (reducedPivotBlock g) =
      reducedPivotBlock (mapRingHom (n := ι) f g) := by
  unfold reducedPivotBlock
  exact reducedPivotBlockAt_mapRingHom g (leastIndex (ι := ι)) _ f

end Least

end Naturality

/-! ## Optional factorisation -/

section Factorization

/-- Recover `g` from its pivot clearers. -/
theorem canonicalPivotUnitAt_factorization (g : GL ι K) (c : ι) :
    let Rclear :=
      rowClear (↑g : Matrix ι ι K) (pivotRow g c) c (pivotRow_ne_zero g c)
    let Cclear :=
      columnClear (↑g : Matrix ι ι K) (pivotRow g c) c (pivotRow_ne_zero g c)
    g = Rclear⁻¹ * canonicalPivotUnitAt g c * Cclear⁻¹ := by
  unfold canonicalPivotUnitAt
  group

/-- Full factorisation with swap alignment. -/
theorem alignedPivotUnitAt_factorization (g : GL ι K) (c : ι) :
    let Rclear :=
      rowClear (↑g : Matrix ι ι K) (pivotRow g c) c (pivotRow_ne_zero g c)
    let Cclear :=
      columnClear (↑g : Matrix ι ι K) (pivotRow g c) c (pivotRow_ne_zero g c)
    let P := pivotPermutation g c
    g = Rclear⁻¹ * P⁻¹ * alignedPivotUnitAt g c * Cclear⁻¹ := by
  intro Rclear Cclear P
  have h_aligned : P * (Rclear * g * Cclear) = alignedPivotUnitAt g c := rfl
  calc g = Rclear⁻¹ * P⁻¹ * (P * (Rclear * g * Cclear)) * Cclear⁻¹ := by group
    _ = Rclear⁻¹ * P⁻¹ * alignedPivotUnitAt g c * Cclear⁻¹ := by rw [h_aligned]

end Factorization

end Matrix.GeneralLinearGroup

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

public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Padding
public import MathlibExt.Analysis.InnerProductSpace.CompactOperator.FiniteRankClosure
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compact matrix corners of finite orthonormal families

For a finite orthonormal family `β_i` in a complete complex Hilbert space, the nonunital star
homomorphism `Φ_β : M_m(ℂ) → K(H)` is `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)`, where `θ_(x,y)z=⟨y,z⟩x`.
It recovers the matrix entries by `⟨β_i,Φ_β(X)β_j⟩=X_ij`, and is injective and isometric.

Matrix identity maps to the orthogonal projection onto the family span. It is the ambient
identity only for a spanning family. Empty families and zero Hilbert spaces are allowed;
top-left zero padding agrees with restricting the larger orthonormal family.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Orthonormal

universe uIndex uHilbert

variable {m : Type uIndex} [Fintype m]
variable {H : Type uHilbert} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {β : m → H}

/-- **Compact matrix corner of an orthonormal family.** Let `H` be a complete complex Hilbert
space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. `compactCorner β` is the nonunital complex star homomorphism `Φ_β :
M_m(ℂ) → K(H)`, with the C-star matrix norm and inherited compact-operator norm. -/
def compactCorner (hβ : Orthonormal ℂ β) :
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    letI : NonUnitalCStarAlgebra
        (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
      (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra;
    CStarMatrix m m ℂ →⋆ₙₐ[ℂ]
      (compactEndomorphismClosedStarIdeal (H := H)).carrier := by
  classical
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let : NonUnitalCStarAlgebra
      (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
    (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra
  let T (X : CStarMatrix m m ℂ) : H →L[ℂ] H :=
    ∑ i, ∑ j, X i j • InnerProductSpace.rankOne ℂ (β i) (β j)
  have hApply (X : CStarMatrix m m ℂ) (z : H) :
      T X z = ∑ i, (∑ j, X i j * inner ℂ (β j) z) • β i := by
    simp only [T, sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
      smul_smul, Finset.sum_smul]
  have hInner (X : CStarMatrix m m ℂ) (z : H) (i : m) :
      inner ℂ (β i) (T X z) = ∑ j, X i j * inner ℂ (β j) z := by
    rw [hApply]
    exact hβ.inner_right_fintype (fun k => ∑ j, X k j * inner ℂ (β j) z) i
  let ρ : CStarMatrix m m ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) :=
    { toFun := T
      map_zero' := by
        simp only [T, CStarMatrix.zero_apply, zero_smul, Finset.sum_const_zero]
      map_add' := by
        intro X Y
        simp only [T, CStarMatrix.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c X
        simp only [T, CStarMatrix.smul_apply, smul_eq_mul, mul_smul,
          Finset.smul_sum, MonoidHom.id_apply]
      map_mul' := by
        intro X Y
        apply ContinuousLinearMap.ext
        intro z
        change T (X * Y) z = T X (T Y z)
        rw [hApply, hApply]
        simp_rw [hInner]
        apply Finset.sum_congr rfl
        intro i _hi
        apply congrArg (fun c : ℂ => c • β i)
        simp_rw [CStarMatrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      map_star' := by
        intro X
        change (∑ i, ∑ j, (star X) i j • InnerProductSpace.rankOne ℂ (β i) (β j)) =
          star (∑ i, ∑ j, X i j • InnerProductSpace.rankOne ℂ (β i) (β j))
        simp only [CStarMatrix.star_apply, star_sum, star_smul,
          ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
        exact Finset.sum_comm }
  refine ρ.codRestrict (compactEndomorphismClosedStarIdeal (H := H)).carrier ?_
  intro X
  have hFinite : T X ∈
      InnerProductSpace.finiteRankSubmodule (𝕜 := ℂ) (E := H) (F := H) := by
    dsimp only [T]
    exact Submodule.sum_mem _ fun i _hi =>
      Submodule.sum_mem _ fun j _hj =>
        Submodule.smul_mem _ (X i j)
          (InnerProductSpace.rankOne_mem_finiteRankSubmodule (β i) (β j))
  change T X ∈ compactEndomorphismIdeal (𝕜 := ℂ) (E := H)
  exact (mem_compactEndomorphismIdeal (T X)).2
    (InnerProductSpace.finiteRankSubmodule_isCompactOperator hFinite)

/-- **Rank-one sum representing the compact corner.** Let `H` be a complete complex Hilbert
space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. for `X ∈ M_m(ℂ)`, the bounded operator underlying `Φ_β(X)` is `Σ_i,j X_ij
θ_(β_i,β_j)`. -/
theorem compactCorner_coe (hβ : Orthonormal ℂ β) (X : CStarMatrix m m ℂ) :
    (hβ.compactCorner X : H →L[ℂ] H) =
      ∑ i, ∑ j, X i j • InnerProductSpace.rankOne ℂ (β i) (β j) :=
  rfl

/-- **Column action of a finite compact matrix corner.** Let `H` be a complete complex Hilbert
space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. for `X ∈ M_m(ℂ)` and `z ∈ H`, `Φ_β(X)z=Σ_i (Σ_j X_ij⟨β_j,z⟩)β_i`. -/
theorem compactCorner_apply (hβ : Orthonormal ℂ β) (X : CStarMatrix m m ℂ) (z : H) :
    (hβ.compactCorner X : H →L[ℂ] H) z =
      ∑ i, (∑ j, X i j * inner ℂ (β j) z) • β i := by
  rw [hβ.compactCorner_coe]
  simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
    smul_smul, Finset.sum_smul]

/-- **Finite matrix column on a family vector.** Let `H` be a complete complex Hilbert space,
`m` a finite index type and `β : m → H` an orthonormal family. Write `θ_(x,y)z=⟨y,z⟩x` and
`Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner `M_m(ℂ) → K(H)`. for `X ∈
M_m(ℂ)` and `j ∈ m`, `Φ_β(X)β_j=Σ_i X_ij β_i`. -/
theorem compactCorner_basis (hβ : Orthonormal ℂ β) (X : CStarMatrix m m ℂ) (j : m) :
    (hβ.compactCorner X : H →L[ℂ] H) (β j) = ∑ i, X i j • β i := by
  classical
  rw [hβ.compactCorner_apply]
  simp [orthonormal_iff_ite.mp hβ]

/-- **Recovery of a compact corner matrix entry.** Let `H` be a complete complex Hilbert
space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. for `X ∈ M_m(ℂ)` and `i,j ∈ m`, `⟨β_i,Φ_β(X)β_j⟩=X_ij`, using the complex
inner product linear in its second argument. -/
theorem compactCorner_inner (hβ : Orthonormal ℂ β) (X : CStarMatrix m m ℂ) (i j : m) :
    inner ℂ (β i) ((hβ.compactCorner X : H →L[ℂ] H) (β j)) = X i j := by
  rw [hβ.compactCorner_basis]
  exact hβ.inner_right_fintype (fun k => X k j) i

/-- **Injectivity of a finite orthonormal matrix corner.** Let `H` be a complete complex
Hilbert space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. the map `Φ_β` is injective; the orthonormal family need not span `H`. -/
theorem compactCorner_injective (hβ : Orthonormal ℂ β) :
    Function.Injective hβ.compactCorner := by
  intro X Y hXY
  apply CStarMatrix.ext
  intro i j
  have hEntry := congrArg
    (fun T : (compactEndomorphismClosedStarIdeal (H := H)).carrier =>
      inner ℂ (β i) ((T : H →L[ℂ] H) (β j))) hXY
  simpa only [hβ.compactCorner_inner] using hEntry

/-- **Metric isometry of a finite compact matrix corner.** Let `H` be a complete complex
Hilbert space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. `Φ_β` is an isometry between the C-star matrix metric and the inherited
operator-norm metric on `K(H)`. -/
theorem compactCorner_isometry (hβ : Orthonormal ℂ β) :
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    letI : NonUnitalCStarAlgebra
        (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
      (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra;
    Isometry hβ.compactCorner := by
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let : NonUnitalCStarAlgebra
      (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
    (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra
  exact NonUnitalStarAlgHom.isometry hβ.compactCorner hβ.compactCorner_injective

/-- **Norm preservation of an orthonormal matrix corner.** Let `H` be a complete complex
Hilbert space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. for every `X ∈ M_m(ℂ)`, `‖Φ_β(X)‖=‖X‖`. -/
theorem compactCorner_norm (hβ : Orthonormal ℂ β) (X : CStarMatrix m m ℂ) :
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ;
    letI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ;
    letI : NonUnitalCStarAlgebra
        (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
      (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra;
    ‖hβ.compactCorner X‖ = ‖X‖ := by
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  let : NonUnitalCStarAlgebra
      (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
    (compactEndomorphismClosedStarIdeal (H := H)).carrierCStarAlgebra
  exact NonUnitalStarAlgHom.norm_map hβ.compactCorner hβ.compactCorner_injective X

/-- **Matrix identity gives the finite family projection.** Let `H` be a complete complex
Hilbert space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. with decidable equality on `m`, `Φ_β(I_m)=Σ_i θ_(β_i,β_i)`, the
orthogonal projection onto the finite family span. -/
theorem compactCorner_one [DecidableEq m] (hβ : Orthonormal ℂ β) :
    (hβ.compactCorner (1 : CStarMatrix m m ℂ) : H →L[ℂ] H) =
      ∑ i, InnerProductSpace.rankOne ℂ (β i) (β i) := by
  rw [hβ.compactCorner_coe]
  simp [CStarMatrix.one_apply]

/-- **Star projection from a corner matrix identity.** Let `H` be a complete complex Hilbert
space, `m` a finite index type and `β : m → H` an orthonormal family. Write
`θ_(x,y)z=⟨y,z⟩x` and `Φ_β(X)=Σ_i,j X_ij θ_(β_i,β_j)` for the nonunital matrix corner
`M_m(ℂ) → K(H)`. with decidable equality on `m`, `Φ_β(I_m)` satisfies `P²=P` and `P*=P`. -/
theorem compactCorner_one_isStarProjection [DecidableEq m] (hβ : Orthonormal ℂ β) :
    IsStarProjection (hβ.compactCorner (1 : CStarMatrix m m ℂ) : H →L[ℂ] H) :=
  ((IsStarProjection.one (CStarMatrix m m ℂ)).map hβ.compactCorner).map
    (NonUnitalStarSubalgebraClass.subtype
      (compactEndomorphismClosedStarIdeal (H := H)).carrier)

/-- **Top-left padding agrees with restricting an orthonormal family.** Let `H` be a complete
complex Hilbert space, `r≤s` natural numbers and `γ : Fin s → H` orthonormal. If `γ_r` is
its restriction along `Fin.castLE`, then for `X ∈ M_r(ℂ)`, `Φ_γ(zeroExtend X)=Φ_(γ_r)(X)`.
The case `r=0` is allowed. -/
theorem compactCorner_zeroExtend {r s : ℕ} (h : r ≤ s) {γ : Fin s → H}
    (hγ : Orthonormal ℂ γ) (X : CStarMatrix (Fin r) (Fin r) ℂ) :
    hγ.compactCorner (CStarMatrix.zeroExtendStarAlgHom h X) =
      (hγ.comp (Fin.castLE h)
        (fun _i _j hij => Fin.ext (congrArg (fun k : Fin s => k.val) hij))).compactCorner X := by
  apply Subtype.ext
  rw [compactCorner_coe, compactCorner_coe]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hTailRow (i : Fin d) :
      (∑ j : Fin (r + d),
        CStarMatrix.zeroExtendStarAlgHom h X (Fin.natAdd r i) j •
          InnerProductSpace.rankOne ℂ (γ (Fin.natAdd r i)) (γ j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    have hi : ¬(Fin.natAdd r i).val < r :=
      Nat.not_lt.mpr (Nat.le_add_right r i.val)
    simp only [CStarMatrix.zeroExtendStarAlgHom_apply_entry, hi, ↓reduceDIte, zero_smul]
  rw [Fin.sum_trunc _ hTailRow]
  apply Finset.sum_congr rfl
  intro i _hi
  have hTailCol (j : Fin d) :
      CStarMatrix.zeroExtendStarAlgHom h X (Fin.castAdd d i) (Fin.natAdd r j) •
        InnerProductSpace.rankOne ℂ (γ (Fin.castAdd d i)) (γ (Fin.natAdd r j)) = 0 := by
    have hi : (Fin.castAdd d i).val < r := i.isLt
    have hj : ¬(Fin.natAdd r j).val < r :=
      Nat.not_lt.mpr (Nat.le_add_right r j.val)
    simp only [CStarMatrix.zeroExtendStarAlgHom_apply_entry, hi, hj, ↓reduceDIte, zero_smul]
  rw [Fin.sum_trunc _ hTailCol]
  apply Finset.sum_congr rfl
  intro j _hj
  have hiCast : Fin.castAdd d i = Fin.castLE h i := Fin.ext rfl
  have hjCast : Fin.castAdd d j = Fin.castLE h j := Fin.ext rfl
  rw [hiCast, hjCast]
  have hRetained : CStarMatrix.zeroExtendStarAlgHom h X (Fin.castLE h i) (Fin.castLE h j) =
      X i j := by
    simp only [CStarMatrix.zeroExtendStarAlgHom_apply_entry, Fin.val_castLE,
      i.isLt, j.isLt, ↓reduceDIte]
  simpa only [Function.comp_apply] using congrArg
    (fun c : ℂ => c • InnerProductSpace.rankOne ℂ (γ (Fin.castLE h i)) (γ (Fin.castLE h j)))
    hRetained

end Orthonormal

end

end

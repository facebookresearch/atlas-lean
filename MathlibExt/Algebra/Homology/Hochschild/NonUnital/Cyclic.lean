/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Basic
public import MathlibExt.AlgebraicTopology.SemiSimplicialObject.TruncatedAlternatingFaceMapComplex
public import MathlibExt.LinearAlgebra.TensorPower.Cyclic
public import Mathlib.Algebra.Homology.AlternatingConst
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Mathlib.Data.Finset.NatAntidiagonal

import Mathlib.Tactic.Abel
public meta import Lean.Elab.Tactic.Omega

/-!
# Cyclic operators and the regular nonunital Hochschild faces

The regular bar is the bar with the left multiplication
and right multiplication representations. Its truncated differential
comes from the general last-face truncation. Cyclic maps and norms use the
computed tensor-power action in the same original first-factor coordinates.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v w
universe x

namespace ModuleCat.Algebra.Hochschild

/-- Merging the first pair of a tuple includes the original coefficient in its ordered product. -/
theorem mulAdjacent_cons_zero {B : Type w} [Mul B] (n : ℕ) (m : B)
    (a : Fin (n + 1) → B) :
    hochschildMulAdjacent (0 : Fin (n + 1)) (Fin.cons m a) =
      Fin.cons (m * a 0) (hochschildDropFirst a) := by
  funext j
  cases j using Fin.cases <;>
    simp [hochschildMulAdjacent, hochschildDropFirst, Fin.succ_succAbove_succ]

/-- Merging a pair after the coefficient commutes with including the coefficient. -/
theorem mulAdjacent_cons_succ {B : Type w} [Mul B] {n : ℕ} (i : Fin n) (m : B)
    (a : Fin (n + 1) → B) :
    hochschildMulAdjacent i.succ (Fin.cons m a) = Fin.cons m (hochschildMulAdjacent i a) := by
  funext j
  cases j using Fin.cases with
  | zero =>
    have h : (0 : Fin (n + 1)) ≠ i.succ := by
      intro hh
      have hv := congrArg (fun j : Fin (n + 1) => j.val) hh
      change (0 : ℕ) = i.val + 1 at hv
      omega
    unfold hochschildMulAdjacent
    rw [Fin.cons_zero, ite_eq_right h, Fin.succ_succAbove_zero, Fin.cons_zero]
  | succ j =>
    rw [Fin.cons_succ]
    unfold hochschildMulAdjacent
    by_cases h : j = i
    · subst j
      rw [ite_eq_left rfl, ite_eq_left rfl]
      change a i.castSucc * a i.succ = a i.castSucc * a i.succ
      rfl
    · have h' : j.succ ≠ i.succ := by
        intro hji
        exact h ((Fin.succ_injective _) hji)
      rw [ite_eq_right h', ite_eq_right h, Fin.succ_succAbove_succ, Fin.cons_succ]

/-- Inverse index rotation sends an appended final factor to the first position. -/
theorem rotate_snoc {B : Type w} (n : ℕ) (a : Fin n → B) (b : B) :
    (fun i : Fin (n + 1) => (Fin.snoc (α := fun _ : Fin (n + 1) => B) a b)
      ((finRotate (n + 1)).symm i)) =
      Fin.cons (α := fun _ : Fin (n + 1) => B) b a := by
  funext i
  let t : Fin (n + 1) → B := Fin.cons (α := fun _ : Fin (n + 1) => B) b a
  have h : (Fin.snoc (α := fun _ : Fin (n + 1) => B) a b)
      ((finRotate (n + 1)).symm i) =
      t (finRotate (n + 1) ((finRotate (n + 1)).symm i)) :=
    congrFun (Fin.snoc_eq_cons_rotate (α := B) a b) ((finRotate (n + 1)).symm i)
  exact h.trans (congrArg t ((finRotate (n + 1)).apply_symm_apply i))

end ModuleCat.Algebra.Hochschild

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]

/-- The signed cyclic endomorphism of the original regular tensor level. -/
def cyclicMap (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A n :=
  ModuleCat.ofHom (TensorPower.consCyclicOperator k A n)

/-- The cyclic norm on the same original tensor level. -/
def normMap (n : ℕ) : chainLevel k A A n ⟶ chainLevel k A A n :=
  ModuleCat.ofHom (TensorPower.consNorm k A n)

/-- The maps retain the left norm identity. -/
theorem oneSubCyclicMap_comp_normMap (n : ℕ) :
    (𝟙 (chainLevel k A A n) - cyclicMap k A n) ≫ normMap k A n = 0 := by
  apply ModuleCat.hom_ext
  change TensorPower.consNorm k A n * (1 - TensorPower.consCyclicOperator k A n) = 0
  exact TensorPower.consNorm_mul_one_sub_cyclicOperator k A n

/-- The maps retain the right norm identity. -/
theorem normMap_comp_oneSubCyclicMap (n : ℕ) :
    normMap k A n ≫ (𝟙 (chainLevel k A A n) - cyclicMap k A n) = 0 := by
  apply ModuleCat.hom_ext
  change (1 - TensorPower.consCyclicOperator k A n) * TensorPower.consNorm k A n = 0
  exact TensorPower.consOne_sub_cyclicOperator_mul_norm k A n

/-- An integer residue acts by the cyclic representation on the original level. -/
def cyclicPowerMap (n : ℕ) (j : ℤ) : chainLevel k A A n ⟶ chainLevel k A A n :=
  ModuleCat.ofHom (TensorPower.consCyclicRepresentation k A n
    (Multiplicative.ofAdd (j : ZMod (n + 1))))

/-- The zero residue acts as the identity. -/
@[simp]
theorem cyclicPowerMap_zero (n : ℕ) : cyclicPowerMap k A n 0 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  change TensorPower.consCyclicRepresentation k A n
    (Multiplicative.ofAdd (0 : ZMod (n + 1))) = 1
  exact map_one _

/-- The integer generator is the signed cyclic map. -/
@[simp]
theorem cyclicPowerMap_one (n : ℕ) : cyclicPowerMap k A n 1 = cyclicMap k A n := by
  apply ModuleCat.hom_ext
  change TensorPower.consCyclicRepresentation k A n
    (Multiplicative.ofAdd ((1 : ℤ) : ZMod (n + 1))) = TensorPower.consCyclicOperator k A n
  simpa only [Int.cast_one] using TensorPower.consCyclicRepresentation_generator k A n

/-- Integer addition is composition of the cyclic residue actions. -/
@[reassoc]
theorem cyclicPowerMap_comp (n : ℕ) (i j : ℤ) :
    cyclicPowerMap k A n i ≫ cyclicPowerMap k A n j = cyclicPowerMap k A n (i + j) := by
  apply ModuleCat.hom_ext
  change TensorPower.consCyclicRepresentation k A n (Multiplicative.ofAdd (j : ZMod (n + 1))) *
      TensorPower.consCyclicRepresentation k A n (Multiplicative.ofAdd (i : ZMod (n + 1))) =
    TensorPower.consCyclicRepresentation k A n
      (Multiplicative.ofAdd ((i + j : ℤ) : ZMod (n + 1)))
  rw [← map_mul]
  congr 1
  change Multiplicative.ofAdd ((j : ZMod (n + 1)) + (i : ZMod (n + 1))) = _
  simp only [Int.cast_add, add_comm]

/-- The finite-group norm is invariant before every residue action. -/
@[reassoc]
theorem normMap_comp_cyclicPowerMap (n : ℕ) (j : ℤ) :
    normMap k A n ≫ cyclicPowerMap k A n j = normMap k A n := by
  apply ModuleCat.hom_ext
  change (TensorPower.consCyclicRepresentation k A n
      (Multiplicative.ofAdd (j : ZMod (n + 1)))).comp (TensorPower.consNorm k A n) =
    TensorPower.consNorm k A n
  rw [TensorPower.consNorm_eq_representation_norm]
  exact Representation.self_comp_norm _ _

/-- The same native finite-group norm is invariant after every residue action. -/
@[reassoc]
theorem cyclicPowerMap_comp_normMap (n : ℕ) (j : ℤ) :
    cyclicPowerMap k A n j ≫ normMap k A n = normMap k A n := by
  apply ModuleCat.hom_ext
  change (TensorPower.consNorm k A n).comp
      (TensorPower.consCyclicRepresentation k A n
        (Multiplicative.ofAdd (j : ZMod (n + 1)))) = TensorPower.consNorm k A n
  rw [TensorPower.consNorm_eq_representation_norm]
  exact Representation.norm_comp_self _ _

/-- The norm is the sum of the nonnegative residue actions. -/
theorem normMap_sum_power (n : ℕ) :
    normMap k A n = ∑ j ∈ Finset.range (n + 1), cyclicPowerMap k A n (j : ℤ) := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  change TensorPower.consNorm k A n =
    ∑ j ∈ Finset.range (n + 1), TensorPower.consCyclicRepresentation k A n
      (Multiplicative.ofAdd ((j : ℤ) : ZMod (n + 1)))
  rw [TensorPower.consNorm_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Int.cast_natCast] using (TensorPower.consCyclicRepresentation_natCast k A n j).symm

/-- Inversion permutes the finite cyclic group, giving the inverse-residue norm sum. -/
theorem normMap_sum_inverse_power (n : ℕ) :
    normMap k A n = ∑ j ∈ Finset.range (n + 1), cyclicPowerMap k A n (-(j : ℤ)) := by
  classical
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  simp only [normMap, cyclicPowerMap, ModuleCat.hom_ofHom]
  rw [TensorPower.consNorm_eq_representation_norm]
  let ρ : Representation k (Multiplicative (ZMod (n + 1)))
      (A ⊗[k] TensorPower k n A) := TensorPower.consCyclicRepresentation k A n
  let e : Fin (n + 1) ≃ Multiplicative (ZMod (n + 1)) :=
    (ZMod.finEquiv (n + 1)).toEquiv.trans
      (Multiplicative.ofAdd.trans (Equiv.inv (Multiplicative (ZMod (n + 1)))))
  have he (i : Fin (n + 1)) :
      e i = Multiplicative.ofAdd ((-(i.val : ℤ)) : ZMod (n + 1)) := by
    change (Multiplicative.ofAdd ((ZMod.finEquiv (n + 1)) i))⁻¹ = _
    rw [← ofAdd_neg]
    apply congrArg Multiplicative.ofAdd
    have hFin : (ZMod.finEquiv (n + 1)) i = (i.val : ZMod (n + 1)) :=
      (ZMod.natCast_zmod_val ((ZMod.finEquiv (n + 1)) i)).symm
    have hInt : ((i.val : ℤ) : ZMod (n + 1)) = (i.val : ZMod (n + 1)) :=
      Int.cast_natCast i.val
    exact congrArg (fun z : ZMod (n + 1) => -z) (hFin.trans hInt.symm)
  calc
    ρ.norm = ∑ i : Fin (n + 1), ρ (e i) :=
      (Fintype.sum_equiv e (fun i : Fin (n + 1) => ρ (e i))
        (fun g : Multiplicative (ZMod (n + 1)) => ρ g) fun _ => rfl).symm
    _ = ∑ i : Fin (n + 1), ρ (Multiplicative.ofAdd ((-(i.val : ℤ)) : ZMod (n + 1))) :=
      Finset.sum_congr rfl fun i _ => congrArg ρ (he i)
    _ = _ := by
      simpa only [ρ, Int.cast_neg, Int.cast_natCast] using
        (Fin.sum_univ_eq_sum_range
          (fun j : ℕ => TensorPower.consCyclicRepresentation k A n
            (Multiplicative.ofAdd ((-(j : ℤ)) : ZMod (n + 1)))) (n + 1))

section Multiplication

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- The original nonunital bar with its regular coefficient actions. -/
abbrev regularBar : SemiSimplicialObject (ModuleCat.{max u v} k) :=
  bar (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
    (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m)

/-- The regular bar object is the original coefficient-and-word tensor level. -/
@[simp]
theorem regularBar_obj (n : ℕ) : (regularBar k A) _⦋n⦌ₛ = chainLevel k A A n := rfl

/-- The original regular Hochschild face; no new face model is chosen. -/
abbrev regularFace (n : ℕ) (i : Fin (n + 2)) :
    chainLevel k A A (n + 1) ⟶ chainLevel k A A n :=
  face (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
    (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m) n i

/-- The full differential is the regular nonunital Hochschild complex. -/
abbrev bComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  complex (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
    (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m)

/-- The truncated regular complex, retaining its original degree-zero term. -/
abbrev bPrimeComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (truncatedAlternatingFaceMapComplex (ModuleCat.{max u v} k)).obj (regularBar k A)

/-- Both complexes use the original regular tensor level in each degree. -/
theorem bPrimeComplex_X (n : ℕ) : (bPrimeComplex k A).X n = chainLevel k A A n := rfl

/-- The truncated differential is the sum of the original faces except the final one. -/
theorem bPrimeComplex_d (n : ℕ) :
    (bPrimeComplex k A).d (n + 1) n =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularFace k A n i.castSucc := by
  have hD : (bPrimeComplex k A).d (n + 1) n =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • (regularBar k A).δ i.castSucc :=
    truncatedAlternatingFaceMapComplex_obj_d (C := ModuleCat.{max u v} k)
      (regularBar k A) n
  refine hD.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  have hδ : (regularBar k A).δ i.castSucc = regularFace k A n i.castSucc :=
    ModuleCat.Algebra.Hochschild.NonUnital.bar_δ
      (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
      (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m)
      n i.castSucc
  exact congrArg (fun f : chainLevel k A A (n + 1) ⟶ chainLevel k A A n =>
    (-1 : ℤ) ^ i.val • f) hδ

/-- The full differential retains every original face and sign. -/
theorem bComplex_d (n : ℕ) :
    (bComplex k A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • regularFace k A n i :=
  complex_d _ _ _ n

/-- The first original regular face multiplies the coefficient on the right. -/
theorem regularFace_first_tprod (n : ℕ) (m : A) (a : Fin (n + 1) → A) :
    (regularFace k A n 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (m * a 0) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a) := by
  simpa only [regularRight_apply] using
    (face_first_tprod (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
      (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m) n m a)

/-- The interior original regular face preserves the order of the two adjacent factors. -/
theorem regularFace_inner_tprod (n : ℕ) (i : Fin n) (m : A) (a : Fin (n + 1) → A) :
    (regularFace k A n i.castSucc.succ).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent i a) :=
  face_inner_tprod _ _ _ n i m a

/-- The final original regular face multiplies on the left. -/
theorem regularFace_last_tprod (n : ℕ) (m : A) (a : Fin (n + 1) → A) :
    (regularFace k A n (Fin.last (n + 1))).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a (Fin.last n) * m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) := by
  exact face_last_tprod (NonUnitalAlgHom.lmul k A) (regularRight (k := k) (A := A))
    (fun a b m => regular_commute (k := k) (A := A) a (MulOpposite.unop b) m) n m a

/-- The truncated first differential is multiplication, with no unit assumption. -/
theorem bPrimeComplex_d_one_tprod (m : A) (a : Fin 1 → A) :
    ((bPrimeComplex k A).d 1 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (m * a 0) ⊗ₜ[k] PiTensorProduct.tprod k (fun i : Fin 0 => a i.succ) := by
  have hsum : (∑ i : Fin 1, (-1 : ℤ) ^ i.val • regularFace k A 0 i.castSucc) =
      regularFace k A 0 0 := by
    have h := Fin.sum_univ_one
      (fun i : Fin 1 => (-1 : ℤ) ^ i.val • regularFace k A 0 i.castSucc)
    simpa only [Fin.val_zero, pow_zero, one_smul, Fin.castSucc_zero] using h
  have hd : (bPrimeComplex k A).d 1 0 = regularFace k A 0 0 :=
    (bPrimeComplex_d k A 0).trans hsum
  have hval : ((bPrimeComplex k A).d 1 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (regularFace k A 0 0).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) :=
    congrArg (fun f : chainLevel k A A 1 ⟶ chainLevel k A A 0 =>
      f.hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) hd
  exact hval.trans (regularFace_first_tprod k A 0 m a)

/-- The first atomic cyclic-face identity on the original linear maps. -/
theorem regularFace_zero_cyclic (n : ℕ) :
    (regularFace k A n 0).hom.comp (TensorPower.consCyclicOperator k A (n + 1)) =
      (-1 : k) ^ (n + 1) • (regularFace k A n (Fin.last (n + 1))).hom := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  let t : Fin (n + 2) → A := Fin.cons (α := fun _ : Fin (n + 2) => A) m a
  let s : Fin (n + 1) → A := fun i => t i.castSucc
  let f : (A ⊗[k] TensorPower k (n + 1) A) →ₗ[k] (A ⊗[k] TensorPower k n A) :=
    (regularFace k A n 0).hom
  let g : (A ⊗[k] TensorPower k (n + 1) A) →ₗ[k] (A ⊗[k] TensorPower k n A) :=
    (regularFace k A n (Fin.last (n + 1))).hom
  have ht₀ : t 0 = m := by
    change (Fin.cons (α := fun _ : Fin (n + 2) => A) m a) 0 = m
    exact Fin.cons_zero (n := n + 1) (α := fun _ : Fin (n + 2) => A) m a
  have htail : Fin.tail t = a :=
    Fin.tail_cons (n := n + 1) (α := fun _ : Fin (n + 2) => A) m a
  have hlast : t (Fin.last (n + 1)) = a (Fin.last n) := by
    change (Fin.cons (α := fun _ : Fin (n + 2) => A) m a) (Fin.last n).succ = _
    exact Fin.cons_succ (n := n + 1) (α := fun _ : Fin (n + 2) => A) m a (Fin.last n)
  have ht :
      TensorPower.consCyclicOperator k A (n + 1)
          (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        (-1 : k) ^ (n + 1) • (a (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k s) := by
    simpa only [ht₀, htail, hlast] using
      TensorPower.consCyclicOperator_tmul k A (n + 1) t
  have hs₀ : s 0 = m := ht₀
  have hdrop : hochschildDropFirst s = hochschildDropLast a := by
    funext i
    change (Fin.cons (α := fun _ : Fin (n + 2) => A) m a) i.castSucc.succ = a i.castSucc
    exact Fin.cons_succ (n := n + 1) (α := fun _ : Fin (n + 2) => A) m a i.castSucc
  have hf : f (a (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k s) =
      (a (Fin.last n) * m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) := by
    simpa only [hs₀, hdrop] using regularFace_first_tprod k A n (a (Fin.last n)) s
  have hg : g (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a (Fin.last n) * m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a) :=
    regularFace_last_tprod k A n m a
  change f (TensorPower.consCyclicOperator k A (n + 1)
    (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      (-1 : k) ^ (n + 1) • g (m ⊗ₜ[k] PiTensorProduct.tprod k a)
  calc
    _ = f ((-1 : k) ^ (n + 1) • (a (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k s)) :=
      congrArg f ht
    _ = (-1 : k) ^ (n + 1) • f (a (Fin.last n) ⊗ₜ[k] PiTensorProduct.tprod k s) :=
      f.map_smul _ _
    _ = (-1 : k) ^ (n + 1) •
        ((a (Fin.last n) * m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a)) :=
      congrArg (fun x : A ⊗[k] TensorPower k n A => (-1 : k) ^ (n + 1) • x) hf
    _ = (-1 : k) ^ (n + 1) • g (m ⊗ₜ[k] PiTensorProduct.tprod k a) :=
      congrArg (fun x : A ⊗[k] TensorPower k n A => (-1 : k) ^ (n + 1) • x) hg.symm

/-- Every non-wrapping original regular face is the adjacent merge in full coordinates. -/
theorem regularFace_cons_tprod (n : ℕ) (i : Fin (n + 1)) (m : A)
    (a : Fin (n + 1) → A) :
    TensorPower.consEquiv k A n
        ((regularFace k A n i.castSucc).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      PiTensorProduct.tprod k (hochschildMulAdjacent i (Fin.cons m a)) := by
  cases i using Fin.cases with
  | zero =>
    simpa only [Fin.castSucc_zero, TensorPower.consEquiv_tmul, mulAdjacent_cons_zero] using
      congrArg (TensorPower.consEquiv k A n) (regularFace_first_tprod k A n m a)
  | succ i =>
    change TensorPower.consEquiv k A n
        ((regularFace k A n i.castSucc.succ).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
    rw [regularFace_inner_tprod, TensorPower.consEquiv_tmul, mulAdjacent_cons_succ]

/-- The remaining atomic cyclic-face identity preserves every ordered adjacent product. -/
theorem regularFace_succ_cyclic (n : ℕ) (i : Fin (n + 1)) :
    (regularFace k A n i.succ).hom.comp (TensorPower.consCyclicOperator k A (n + 1)) =
      -((TensorPower.consCyclicOperator k A n).comp (regularFace k A n i.castSucc).hom) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  apply (TensorPower.consEquiv k A n).injective
  let u : Fin (n + 2) → A := Fin.cons m a
  have ht :
      TensorPower.consCyclicOperator k A (n + 1)
          (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        (-1 : k) ^ (n + 1) •
          (u (Fin.last (n + 1)) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init u)) := by
    simpa only [u, Fin.cons_zero, Fin.tail_cons, Fin.init_def] using
      TensorPower.consCyclicOperator_tmul k A (n + 1) u
  change TensorPower.consEquiv k A n
      ((regularFace k A n i.succ).hom
        (TensorPower.consCyclicOperator k A (n + 1)
          (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    TensorPower.consEquiv k A n
      (-TensorPower.consCyclicOperator k A n
        ((regularFace k A n i.castSucc).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)))
  refine Fin.lastCases ?_ (fun p => ?_) i
  · let v : Fin (n + 1) → A := Fin.cons
      (u (Fin.last n).castSucc * u (Fin.last n).succ) (Fin.init (Fin.init u))
    have hL : TensorPower.consEquiv k A n
        ((regularFace k A n (Fin.last (n + 1))).hom
          (TensorPower.consCyclicOperator k A (n + 1)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
        (-1 : k) ^ (n + 1) • PiTensorProduct.tprod k v := by
      rw [ht, map_smul, map_smul, regularFace_last_tprod, TensorPower.consEquiv_tmul]
      rfl
    have hR : TensorPower.consEquiv k A n
        (TensorPower.consCyclicOperator k A n
          ((regularFace k A n (Fin.last n).castSucc).hom
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
        (-1 : k) ^ n • PiTensorProduct.tprod k v := by
      rw [TensorPower.consCyclicOperator_coordinates, regularFace_cons_tprod,
        TensorPower.cyclicOperator_tprod, hochschildMulAdjacent_last_snoc,
        ModuleCat.Algebra.Hochschild.rotate_snoc]
    have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
      apply Fin.ext
      rfl
    rw [hlast, hL, map_neg, hR]
    simp only [pow_succ, mul_neg, mul_one, neg_smul]
  · let v : Fin (n + 1) → A :=
      Fin.cons (u (Fin.last (n + 1))) (hochschildMulAdjacent p (Fin.init u))
    have hL : TensorPower.consEquiv k A n
        ((regularFace k A n p.castSucc.succ).hom
          (TensorPower.consCyclicOperator k A (n + 1)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
        (-1 : k) ^ (n + 1) • PiTensorProduct.tprod k v := by
      change TensorPower.consEquiv k A n
          ((regularFace k A n p.succ.castSucc).hom
            (TensorPower.consCyclicOperator k A (n + 1)
              (m ⊗ₜ[k] PiTensorProduct.tprod k a))) = _
      rw [ht, map_smul, map_smul, regularFace_cons_tprod, mulAdjacent_cons_succ]
    have hR : TensorPower.consEquiv k A n
        (TensorPower.consCyclicOperator k A n
          ((regularFace k A n p.castSucc.castSucc).hom
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
        (-1 : k) ^ n • PiTensorProduct.tprod k v := by
      rw [TensorPower.consCyclicOperator_coordinates, regularFace_cons_tprod,
        TensorPower.cyclicOperator_tprod, hochschildMulAdjacent_castSucc_snoc,
        ModuleCat.Algebra.Hochschild.rotate_snoc]
    rw [hL, map_neg, hR]
    simp only [pow_succ, mul_neg, mul_one, neg_smul]

/-- The first original face has the printed integer-sign cyclic identity. -/
theorem regularFace_zero_cyclicMap (n : ℕ) :
    cyclicMap k A (n + 1) ≫ regularFace k A n 0 =
      (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1)) := by
  apply ModuleCat.hom_ext
  change (regularFace k A n 0).hom.comp (TensorPower.consCyclicOperator k A (n + 1)) =
    ((-1 : ℤ) ^ (n + 1)) • (regularFace k A n (Fin.last (n + 1))).hom
  rw [← Int.cast_smul_eq_zsmul k]
  simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using regularFace_zero_cyclic k A n

/-- Every shifted original face has the printed negative cyclic identity. -/
theorem regularFace_succ_cyclicMap (n : ℕ) (i : Fin (n + 1)) :
    cyclicMap k A (n + 1) ≫ regularFace k A n i.succ =
      -(regularFace k A n i.castSucc ≫ cyclicMap k A n) := by
  apply ModuleCat.hom_ext
  change (regularFace k A n i.succ).hom.comp (TensorPower.consCyclicOperator k A (n + 1)) =
    -((TensorPower.consCyclicOperator k A n).comp (regularFace k A n i.castSucc).hom)
  exact regularFace_succ_cyclic k A n i

/-- Actual inverse residue actions express every signed face through the first face. -/
theorem regularFace_weighted_conjugate (n : ℕ) (i : Fin (n + 2)) :
    (-1 : ℤ) ^ i.val • regularFace k A n i =
      cyclicPowerMap k A (n + 1) (-(i.val : ℤ)) ≫ regularFace k A n 0 ≫
        cyclicPowerMap k A n (i.val : ℤ) := by
  induction i using Fin.induction with
  | zero =>
    simp only [Fin.val_zero, pow_zero, one_smul, Nat.cast_zero, neg_zero,
      cyclicPowerMap_zero, Category.id_comp, Category.comp_id]
  | succ i ih =>
    simp only [Fin.val_castSucc] at ih
    have hs : regularFace k A n i.succ =
        -(cyclicPowerMap k A (n + 1) (-1) ≫ regularFace k A n i.castSucc ≫
          cyclicPowerMap k A n 1) := by
      have h := congrArg
        (fun f : chainLevel k A A (n + 1) ⟶ chainLevel k A A n =>
          cyclicPowerMap k A (n + 1) (-1) ≫ f)
        (regularFace_succ_cyclicMap k A n i)
      simpa only [← cyclicPowerMap_one, ← Category.assoc, cyclicPowerMap_comp,
        neg_add_cancel, cyclicPowerMap_zero, Category.id_comp, comp_neg] using h
    have hsource : (-1 : ℤ) + -(i.val : ℤ) = -((i.val + 1 : ℕ) : ℤ) := by omega
    have htarget : (i.val : ℤ) + 1 = ((i.val + 1 : ℕ) : ℤ) := by omega
    calc
      (-1 : ℤ) ^ i.succ.val • regularFace k A n i.succ =
          cyclicPowerMap k A (n + 1) (-1) ≫
            ((-1 : ℤ) ^ i.val • regularFace k A n i.castSucc) ≫ cyclicPowerMap k A n 1 := by
        rw [hs]
        simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, smul_neg,
          neg_neg, comp_zsmul, zsmul_comp]
      _ = cyclicPowerMap k A (n + 1) (-1) ≫
          (cyclicPowerMap k A (n + 1) (-(i.val : ℤ)) ≫ regularFace k A n 0 ≫
            cyclicPowerMap k A n (i.val : ℤ)) ≫ cyclicPowerMap k A n 1 := by rw [ih]
      _ = _ := by
        simp only [Category.assoc, cyclicPowerMap_comp_assoc, cyclicPowerMap_comp,
          hsource, htarget, Fin.val_succ]

/-- The cyclic norm intertwines the full and truncated regular differentials. -/
theorem normMap_comp_bPrime_d (n : ℕ) :
    normMap k A (n + 1) ≫ (bPrimeComplex k A).d (n + 1) n =
      (bComplex k A).d (n + 1) n ≫ normMap k A n := by
  let d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bComplex k A).d (n + 1) n
  let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
  have hd : d = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • regularFace k A n i :=
    bComplex_d k A n
  have hd' : d' = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularFace k A n i.castSucc :=
    bPrimeComplex_d k A n
  change normMap k A (n + 1) ≫ d' = d ≫ normMap k A n
  have htarget :
      (∑ i : Fin (n + 1), cyclicPowerMap k A n (i.val : ℤ)) = normMap k A n := by
    rw [normMap_sum_power]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => cyclicPowerMap k A n (j : ℤ)) (n + 1)
  have hsource :
      (∑ i : Fin (n + 2), cyclicPowerMap k A (n + 1) (-(i.val : ℤ))) =
        normMap k A (n + 1) := by
    rw [normMap_sum_inverse_power]
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => cyclicPowerMap k A (n + 1) (-(j : ℤ))) (n + 2)
  have hleft : normMap k A (n + 1) ≫ d' =
      normMap k A (n + 1) ≫ regularFace k A n 0 ≫ normMap k A n := by
    calc
      _ = ∑ i : Fin (n + 1),
          normMap k A (n + 1) ≫ ((-1 : ℤ) ^ i.val • regularFace k A n i.castSucc) := by
        rw [hd', comp_sum]
      _ = ∑ i : Fin (n + 1),
          normMap k A (n + 1) ≫ regularFace k A n 0 ≫ cyclicPowerMap k A n (i.val : ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := regularFace_weighted_conjugate k A n i.castSucc
        simp only [Fin.val_castSucc] at hi
        rw [hi]
        simp only [Category.assoc, normMap_comp_cyclicPowerMap_assoc]
      _ = _ := by
        simp only [← Category.assoc, ← comp_sum, htarget]
  have hright : d ≫ normMap k A n =
      normMap k A (n + 1) ≫ regularFace k A n 0 ≫ normMap k A n := by
    calc
      _ = ∑ i : Fin (n + 2),
          ((-1 : ℤ) ^ i.val • regularFace k A n i) ≫ normMap k A n := by
        rw [hd, sum_comp]
      _ = ∑ i : Fin (n + 2), cyclicPowerMap k A (n + 1) (-(i.val : ℤ)) ≫
          regularFace k A n 0 ≫ normMap k A n := by
        apply Finset.sum_congr rfl
        intro i _
        rw [regularFace_weighted_conjugate k A n i]
        simp only [Category.assoc, cyclicPowerMap_comp_normMap]
      _ = _ := by rw [← sum_comp, hsource]
  exact hleft.trans hright.symm

/-- Splitting off the final face compares the full and truncated boundaries. -/
theorem bComplex_d_eq_bPrime_add_last (n : ℕ) :
    (bComplex k A).d (n + 1) n =
      let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
      d' + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1)) := by
  let d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bComplex k A).d (n + 1) n
  let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
  have hd : d = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • regularFace k A n i := bComplex_d k A n
  have hd' : d' = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularFace k A n i.castSucc :=
    bPrimeComplex_d k A n
  change d = d' + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1))
  rw [hd, hd', Fin.sum_univ_castSucc]
  rfl

/-- The shifted face sum is the cyclic translate of the truncated boundary. -/
theorem cyclicMap_comp_bComplex_d (n : ℕ) :
    cyclicMap k A (n + 1) ≫ (bComplex k A).d (n + 1) n =
      let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
      d' ≫ cyclicMap k A n + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1)) := by
  let d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bComplex k A).d (n + 1) n
  let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
  have hd : d = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • regularFace k A n i := bComplex_d k A n
  have hd' : d' = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • regularFace k A n i.castSucc :=
    bPrimeComplex_d k A n
  change cyclicMap k A (n + 1) ≫ d =
    d' ≫ cyclicMap k A n + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1))
  rw [hd, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, comp_add]
  rw [regularFace_zero_cyclicMap]
  rw [comp_sum, hd', sum_comp]
  apply (congrArg (fun f => (-1 : ℤ) ^ (n + 1) •
    regularFace k A n (Fin.last (n + 1)) + f) ?_).trans (add_comm _ _)
  apply Finset.sum_congr rfl
  intro i _
  rw [comp_zsmul, regularFace_succ_cyclicMap, zsmul_comp]
  simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, smul_neg, neg_neg]

/-- The two boundaries satisfy the first cyclic commutation square. -/
theorem bPrime_d_comp_oneSub_cyclicMap (n : ℕ) :
    (bPrimeComplex k A).d (n + 1) n ≫ (𝟙 (chainLevel k A A n) - cyclicMap k A n) =
      (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1)) ≫
        (bComplex k A).d (n + 1) n := by
  let d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bComplex k A).d (n + 1) n
  let d' : chainLevel k A A (n + 1) ⟶ chainLevel k A A n := (bPrimeComplex k A).d (n + 1) n
  have hlast : d = d' + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1)) :=
    bComplex_d_eq_bPrime_add_last k A n
  have hcyclic : cyclicMap k A (n + 1) ≫ d =
      d' ≫ cyclicMap k A n + (-1 : ℤ) ^ (n + 1) • regularFace k A n (Fin.last (n + 1)) :=
    cyclicMap_comp_bComplex_d k A n
  change d' ≫ (𝟙 (chainLevel k A A n) - cyclicMap k A n) =
    (𝟙 (chainLevel k A A (n + 1)) - cyclicMap k A (n + 1)) ≫ d
  rw [comp_sub, sub_comp, Category.comp_id, Category.id_comp,
    hcyclic, hlast]
  abel

/-- The first cyclic square gives the map from the truncated column to the full one. -/
def oneSubCyclicChainMap : bPrimeComplex k A ⟶ bComplex k A :=
  ChainComplex.ofHom (fun n => 𝟙 (chainLevel k A A n) - cyclicMap k A n)
    (fun n => (bPrime_d_comp_oneSub_cyclicMap k A n).symm)

/-- The norm is a map from the full column to the truncated one. -/
def normChainMap : bComplex k A ⟶ bPrimeComplex k A :=
  ChainComplex.ofHom (normMap k A) (normMap_comp_bPrime_d k A)

/-- The first column map has its original signed cyclic component. -/
@[simp]
theorem oneSubCyclicChainMap_f (n : ℕ) :
    (oneSubCyclicChainMap k A).f n = 𝟙 (chainLevel k A A n) - cyclicMap k A n := rfl

/-- The norm column map has its norm component. -/
@[simp]
theorem normChainMap_f (n : ℕ) : (normChainMap k A).f n = normMap k A n := rfl

/-- Adjacent column maps compose to zero in the first order. -/
theorem oneSubCyclicChainMap_comp_normChainMap :
    oneSubCyclicChainMap k A ≫ normChainMap k A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact oneSubCyclicMap_comp_normMap k A n

/-- They compose to zero in the other order as well. -/
theorem normChainMap_comp_oneSubCyclicChainMap :
    normChainMap k A ≫ oneSubCyclicChainMap k A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  exact normMap_comp_oneSubCyclicMap k A n

/-- Even columns use the original full boundary; odd columns use the truncated boundary. -/
def cyclicColumn (p : ℕ) : ChainComplex (ModuleCat.{max u v} k) ℕ where
  X n := chainLevel k A A n
  d i j := if Even p then (bComplex k A).d i j else (bPrimeComplex k A).d i j
  shape i j hij := by
    let d : chainLevel k A A i ⟶ chainLevel k A A j := (bComplex k A).d i j
    let d' : chainLevel k A A i ⟶ chainLevel k A A j := (bPrimeComplex k A).d i j
    change (if Even p then d else d') = 0
    by_cases hp : Even p
    · rw [ite_eq_left hp]
      exact (bComplex k A).shape i j hij
    · rw [ite_eq_right hp]
      exact (bPrimeComplex k A).shape i j hij
  d_comp_d' i j l _ _ := by
    let d (i j : ℕ) : chainLevel k A A i ⟶ chainLevel k A A j := (bComplex k A).d i j
    let d' (i j : ℕ) : chainLevel k A A i ⟶ chainLevel k A A j := (bPrimeComplex k A).d i j
    change (if Even p then d i j else d' i j) ≫ (if Even p then d j l else d' j l) = 0
    by_cases hp : Even p
    · rw [ite_eq_left hp, ite_eq_left hp]
      exact (bComplex k A).d_comp_d i j l
    · rw [ite_eq_right hp, ite_eq_right hp]
      exact (bPrimeComplex k A).d_comp_d i j l

/-- No bottom term is removed when a column is truncated. -/
@[simp]
theorem cyclicColumn_X (p q : ℕ) : (cyclicColumn k A p).X q = chainLevel k A A q := rfl

/-- An even column is the original full complex, including all of its objects and maps. -/
theorem cyclicColumn_even (p : ℕ) (hp : Even p) :
    cyclicColumn k A p = bComplex k A := by
  refine HomologicalComplex.ext (C₁ := cyclicColumn k A p) (C₂ := bComplex k A)
    (by funext q; rfl) ?_
  intro i j _
  let d : chainLevel k A A i ⟶ chainLevel k A A j := (bComplex k A).d i j
  let d' : chainLevel k A A i ⟶ chainLevel k A A j := (bPrimeComplex k A).d i j
  change (if Even p then d else d') ≫ 𝟙 (chainLevel k A A j) = 𝟙 (chainLevel k A A i) ≫ d
  rw [ite_eq_left hp, Category.comp_id, Category.id_comp]

/-- An odd column is the general last-face truncation. -/
theorem cyclicColumn_odd (p : ℕ) (hp : ¬ Even p) :
    cyclicColumn k A p = bPrimeComplex k A := by
  refine HomologicalComplex.ext (C₁ := cyclicColumn k A p) (C₂ := bPrimeComplex k A)
    (by funext q; rfl) ?_
  intro i j _
  let d : chainLevel k A A i ⟶ chainLevel k A A j := (bComplex k A).d i j
  let d' : chainLevel k A A i ⟶ chainLevel k A A j := (bPrimeComplex k A).d i j
  change (if Even p then d else d') ≫ 𝟙 (chainLevel k A A j) = 𝟙 (chainLevel k A A i) ≫ d'
  rw [ite_eq_right hp, Category.comp_id, Category.id_comp]

/-- The horizontal map alternates the maps 1-t and N, beginning with 1-t. -/
def cyclicHorizontalMap (p : ℕ) : cyclicColumn k A (p + 1) ⟶ cyclicColumn k A p :=
  ChainComplex.ofHom
    (fun q => if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q)
    fun q => by
      let d : chainLevel k A A (q + 1) ⟶ chainLevel k A A q := (bComplex k A).d (q + 1) q
      let d' : chainLevel k A A (q + 1) ⟶ chainLevel k A A q := (bPrimeComplex k A).d (q + 1) q
      change
        (if Even p then 𝟙 (chainLevel k A A (q + 1)) - cyclicMap k A (q + 1)
          else normMap k A (q + 1)) ≫
          (if Even p then d else d') =
        (if Even (p + 1) then d else d') ≫
          (if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q)
      by_cases hp : Even p
      · have hp' : ¬ Even (p + 1) := by
          simpa only [Nat.even_add_one, not_not] using hp
        have hComm :
            (𝟙 (chainLevel k A A (q + 1)) - cyclicMap k A (q + 1)) ≫ d =
              d' ≫ (𝟙 (chainLevel k A A q) - cyclicMap k A q) :=
          (bPrime_d_comp_oneSub_cyclicMap k A q).symm
        simpa only [ite_eq_left hp, ite_eq_right hp'] using hComm
      · have hp' : Even (p + 1) := Nat.even_add_one.mpr hp
        have hComm : normMap k A (q + 1) ≫ d' = d ≫ normMap k A q :=
          normMap_comp_bPrime_d k A q
        simpa only [ite_eq_right hp, ite_eq_left hp'] using hComm

/-- The horizontal component acts on the original tensor level. -/
@[simp]
theorem cyclicHorizontalMap_f (p q : ℕ) :
    (cyclicHorizontalMap k A p).f q =
      if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q := rfl

/-- Both norm identities prove the consecutive horizontal composites vanish. -/
theorem cyclicHorizontalMap_squared (p : ℕ) :
    cyclicHorizontalMap k A (p + 1) ≫ cyclicHorizontalMap k A p = 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  change (if Even (p + 1) then 𝟙 _ - cyclicMap k A q else normMap k A q) ≫
    (if Even p then 𝟙 _ - cyclicMap k A q else normMap k A q) = 0
  by_cases hp : Even p
  · have hp' : ¬ Even (p + 1) := by
      simpa only [Nat.even_add_one, not_not] using hp
    rw [if_neg hp', if_pos hp]
    exact normMap_comp_oneSubCyclicMap k A q
  · have hp' : Even (p + 1) := Nat.even_add_one.mpr hp
    rw [if_pos hp', if_neg hp]
    exact oneSubCyclicMap_comp_normMap k A q

/-- The first-quadrant cyclic bicomplex is a chain complex of its original columns. -/
def cyclicBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ChainComplex.of (cyclicColumn k A) (cyclicHorizontalMap k A)
    (cyclicHorizontalMap_squared k A)

/-- Every bicomplex cell is the original regular tensor level, including the bottom row. -/
@[simp]
theorem cyclicBicomplex_XX (p q : ℕ) :
    ((cyclicBicomplex k A).X p).X q = chainLevel k A A q := rfl

/-- The horizontal differential begins with 1-t and then alternates with N. -/
theorem cyclicBicomplex_horizontal (p q : ℕ) :
    ((cyclicBicomplex k A).d (p + 1) p).f q =
      if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q := by
  have hd : (cyclicBicomplex k A).d (p + 1) p = cyclicHorizontalMap k A p := by
    dsimp only [cyclicBicomplex]
    rw [ChainComplex.of_d]
  exact (HomologicalComplex.congr_hom hd q).trans (cyclicHorizontalMap_f k A p q)

/-- The unsigned vertical differential uses precisely the two original column boundaries. -/
theorem cyclicBicomplex_vertical (p q : ℕ) :
    ((cyclicBicomplex k A).X p).d (q + 1) q =
      if Even p then (bComplex k A).d (q + 1) q else (bPrimeComplex k A).d (q + 1) q := rfl

/-- Native totalization supplies the printed sign on each vertical column. -/
def signedVertical (p q : ℕ) :
    chainLevel k A A (q + 1) ⟶ chainLevel k A A q :=
  (ComplexShape.down ℕ).ε p • ((cyclicBicomplex k A).X p).d (q + 1) q

/-- The native sign is b on even columns and the printed -b' on odd columns. -/
theorem signedVertical_eq (p q : ℕ) :
    signedVertical k A p q =
      if Even p then (bComplex k A).d (q + 1) q else -(bPrimeComplex k A).d (q + 1) q := by
  let d : chainLevel k A A (q + 1) ⟶ chainLevel k A A q :=
    (bComplex k A).d (q + 1) q
  let d' : chainLevel k A A (q + 1) ⟶ chainLevel k A A q :=
    (bPrimeComplex k A).d (q + 1) q
  let v : chainLevel k A A (q + 1) ⟶ chainLevel k A A q :=
    ((cyclicBicomplex k A).X p).d (q + 1) q
  let σ : ℤˣ := (ComplexShape.down ℕ).ε p
  have h₀ : signedVertical k A p q = σ • v := rfl
  have hv : v = if Even p then d else d' := cyclicBicomplex_vertical k A p q
  have hσ : σ = (-1 : ℤˣ) ^ p := ComplexShape.ε_down_ℕ p
  have hParity : σ • (if Even p then d else d') = if Even p then d else -d' := by
    rw [hσ]
    by_cases hp : Even p
    · simp only [if_pos hp, hp.neg_one_pow, one_smul]
    · simp only [if_neg hp, (Nat.not_even_iff_odd.mp hp).neg_one_pow]
      change (-1 : ℤ) • d' = -d'
      exact neg_one_zsmul _
  exact h₀.trans ((congrArg
    (fun f : chainLevel k A A (q + 1) ⟶ chainLevel k A A q => σ • f) hv).trans hParity)

/-- Each horizontal row is the native periodic complex of the cyclic action. -/
def cyclicRow (q : ℕ) : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  HomologicalComplex.alternatingConst (chainLevel k A A q)
    (normMap_comp_oneSubCyclicMap k A q) (oneSubCyclicMap_comp_normMap k A q)
    (fun _ _ => ComplexShape.down_nat_odd_add)

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The native periodic row uses the original tensor object. -/
@[simp]
theorem cyclicRow_X (p q : ℕ) : (cyclicRow k A q).X p = chainLevel k A A q := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- Its native periodic differential is the horizontal component. -/
theorem cyclicRow_d (p q : ℕ) :
    (cyclicRow k A q).d (p + 1) p =
      if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q := by
  by_cases hp : Even p <;>
    simp only [cyclicRow, HomologicalComplex.alternatingConst, ComplexShape.down_Rel,
      Nat.even_add_one, hp, not_true_eq_false, not_false_eq_true, ↓reduceDIte, ↓reduceIte]

/-- Native row construction and the bicomplex use the same horizontal map. -/
theorem cyclicBicomplex_horizontal_eq_row (p q : ℕ) :
    ((cyclicBicomplex k A).d (p + 1) p).f q = (cyclicRow k A q).d (p + 1) p := by
  rw [cyclicBicomplex_horizontal, cyclicRow_d]

/-- Totalization uses the native finite-diagonal coproduct in the module category. -/
abbrev cyclicTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (cyclicBicomplex k A).total (ComplexShape.down ℕ)

/-- The original tensor cell has its total-complex inclusion. -/
def cyclicTotalInclusion (p q : ℕ) :
    chainLevel k A A q ⟶ (cyclicTotal k A).X (p + q) :=
  (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p q (p + q) rfl

/-- Native vertical totalization uses the signed boundary on the original summand. -/
theorem cyclicBicomplex_d₂ (p q : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) p (q + 1) (p + q) =
      signedVertical k A p q ≫ cyclicTotalInclusion k A p q := by
  rw [(cyclicBicomplex k A).d₂_eq (ComplexShape.down ℕ) p
    (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) (p + q) rfl]
  change (ComplexShape.down ℕ).ε p •
      (((cyclicBicomplex k A).X p).d (q + 1) q ≫ cyclicTotalInclusion k A p q) =
    signedVertical k A p q ≫ cyclicTotalInclusion k A p q
  exact (Linear.units_smul_comp _ _ _).symm

/-- Native horizontal totalization has no additional horizontal sign. -/
theorem cyclicBicomplex_d₁ (p q : ℕ) :
    (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) =
      (if Even p then 𝟙 (chainLevel k A A q) - cyclicMap k A q else normMap k A q) ≫
        cyclicTotalInclusion k A p q := by
  let D : HomologicalComplex₂ (ModuleCat.{max u v} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  let d : chainLevel k A A q ⟶ chainLevel k A A q := (D.d (p + 1) p).f q
  let ι : chainLevel k A A q ⟶ (cyclicTotal k A).X (p + q) :=
    cyclicTotalInclusion k A p q
  have h : D.d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) = (1 : ℤˣ) • (d ≫ ι) :=
    D.d₁_eq (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q (p + q) rfl
  have h' : D.d₁ (ComplexShape.down ℕ) (p + 1) q (p + q) = d ≫ ι :=
    h.trans (one_smul ℤˣ (d ≫ ι))
  exact h'.trans (congrArg (fun f : chainLevel k A A q ⟶ chainLevel k A A q => f ≫ ι)
    (cyclicBicomplex_horizontal k A p q))

section Naturality

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Nonunital maps intertwine every regular face with independent carrier universes. -/
theorem regularFace_natural (f : A →ₙₐ[k] B) (n : ℕ) (i : Fin (n + 2)) :
    (TensorPower.consLevelMap (f : A →ₗ[k] B) n).comp (regularFace k A n i).hom =
      (regularFace k B n i).hom.comp (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)) := by
  let F := fun r => TensorPower.consLevelMap (f : A →ₗ[k] B) r
  have hf_apply (x : A) : (f : A →ₗ[k] B) x = f x := rfl
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  change F n ((regularFace k A n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
    (regularFace k B n i).hom (F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a))
  have hInput : F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => f (a r)) := by
    simp only [F, TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod, hf_apply]
  refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun q => ?_) j) i
  · have hA := regularFace_first_tprod k A n m a
    have hB := regularFace_first_tprod k B n (f m) (fun r => f (a r))
    calc
      _ = F n ((m * a 0) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a)) :=
        congrArg (F n) hA
      _ = (f m * f (a 0)) ⊗ₜ[k]
          PiTensorProduct.tprod k (hochschildDropFirst (fun r => f (a r))) := by
        simp only [F, TensorPower.consLevelMap, TensorProduct.map_tmul,
          PiTensorProduct.map_tprod, hf_apply, map_mul, hochschildDropFirst]
        rfl
      _ = (regularFace k B n 0).hom (F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) := by
        rw [hInput]
        exact hB.symm
  · change F n ((regularFace k A n (Fin.last (n + 1))).hom
        (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      (regularFace k B n (Fin.last (n + 1))).hom
        (F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    have hA := regularFace_last_tprod k A n m a
    have hB := regularFace_last_tprod k B n (f m) (fun r => f (a r))
    calc
      _ = F n ((a (Fin.last n) * m) ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a)) :=
        congrArg (F n) hA
      _ = (f (a (Fin.last n)) * f m) ⊗ₜ[k]
          PiTensorProduct.tprod k (hochschildDropLast (fun r => f (a r))) := by
        simp only [F, TensorPower.consLevelMap, TensorProduct.map_tmul,
          PiTensorProduct.map_tprod, hf_apply, map_mul, hochschildDropLast]
        rfl
      _ = (regularFace k B n (Fin.last (n + 1))).hom
          (F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) := by
        rw [hInput]
        exact hB.symm
  · have hA := regularFace_inner_tprod k A n q m a
    have hB := regularFace_inner_tprod k B n q (f m) (fun r => f (a r))
    have hTuple : (fun r => f (hochschildMulAdjacent q a r)) =
        hochschildMulAdjacent q (fun r => f (a r)) := by
      funext r
      simp only [hochschildMulAdjacent]
      split_ifs <;> simp only [map_mul]
    calc
      _ = F n (m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent q a)) :=
        congrArg (F n) hA
      _ = f m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => f (hochschildMulAdjacent q a r)) := by
        simp only [F, TensorPower.consLevelMap, TensorProduct.map_tmul, PiTensorProduct.map_tprod, hf_apply]
      _ = f m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildMulAdjacent q (fun r => f (a r))) :=
        congrArg (fun b => f m ⊗ₜ[k] PiTensorProduct.tprod k b) hTuple
      _ = (regularFace k B n q.castSucc.succ).hom
          (F (n + 1) (m ⊗ₜ[k] PiTensorProduct.tprod k a)) := by
        rw [hInput]
        exact hB.symm

/-- The same face square intertwines any finite integer-weighted selection of original faces. -/
theorem regularFace_sum_natural (f : A →ₙₐ[k] B) (n : ℕ) {I : Type*} [Fintype I]
    (ι : I → Fin (n + 2)) (ε : I → ℤ) :
    (TensorPower.consLevelMap (f : A →ₗ[k] B) n).comp
        (∑ i : I, ε i • (regularFace k A n (ι i)).hom) =
      (∑ i : I, ε i • (regularFace k B n (ι i)).hom).comp
        (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => ε i • z) (DFunLike.congr_fun (regularFace_natural f n (ι i)) x)

/-- The full boundary is natural under nonunital maps, with no unit requirement. -/
theorem bComplex_d_natural (f : A →ₙₐ[k] B) (n : ℕ) :
    (TensorPower.consLevelMap (f : A →ₗ[k] B) n).comp ((bComplex k A).d (n + 1) n).hom =
      ((bComplex k B).d (n + 1) n).hom.comp
        (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)) := by
  have hA := congrArg
    (fun d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n => d.hom) (bComplex_d k A n)
  have hB := congrArg
    (fun d : chainLevel k B B (n + 1) ⟶ chainLevel k B B n => d.hom) (bComplex_d k B n)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul] at hA hB
  rw [hA, hB]
  exact regularFace_sum_natural f n id (fun i => (-1 : ℤ) ^ i.val)

/-- The final-face truncation is natural under the same nonunital map. -/
theorem bPrimeComplex_d_natural (f : A →ₙₐ[k] B) (n : ℕ) :
    (TensorPower.consLevelMap (f : A →ₗ[k] B) n).comp ((bPrimeComplex k A).d (n + 1) n).hom =
      ((bPrimeComplex k B).d (n + 1) n).hom.comp
        (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)) := by
  have hA := congrArg
    (fun d : chainLevel k A A (n + 1) ⟶ chainLevel k A A n => d.hom)
    (bPrimeComplex_d k A n)
  have hB := congrArg
    (fun d : chainLevel k B B (n + 1) ⟶ chainLevel k B B n => d.hom)
    (bPrimeComplex_d k B n)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul] at hA hB
  erw [hA, hB]
  exact regularFace_sum_natural f n Fin.castSucc (fun i => (-1 : ℤ) ^ i.val)

/-- The native universe-lift functors carry the original level map into a common module world. -/
def levelMapLift (f : A →ₗ[k] B) (n : ℕ) :
    (ModuleCat.uliftFunctor.{w, max u v} k).obj (chainLevel k A A n) ⟶
      (ModuleCat.uliftFunctor.{v, max u w} k).obj (chainLevel k B B n) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp
    ((TensorPower.consLevelMap f n).comp ULift.moduleEquiv.toLinearMap))

omit [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B] in
/-- The lifted map applies only the original linear map to the original tensor value. -/
@[simp]
theorem levelMapLift_apply (f : A →ₗ[k] B) (n : ℕ)
    (x : (ModuleCat.uliftFunctor.{w, max u v} k).obj (chainLevel k A A n)) :
    (levelMapLift f n).hom x = ULift.up (TensorPower.consLevelMap f n x.down) := rfl

/-- Independent-universe nonunital maps give bicomplex morphisms after native lifting. -/
def cyclicBicomplexMap (f : A →ₙₐ[k] B) :
    (((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (cyclicBicomplex k A) ⟶
    (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (cyclicBicomplex k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let F := fun n => TensorPower.consLevelMap (f : A →ₗ[k] B) n
  let L := fun n => levelMapLift (f : A →ₗ[k] B) n
  have transport {i j : ℕ} (dA : chainLevel k A A i ⟶ chainLevel k A A j)
      (dB : chainLevel k B B i ⟶ chainLevel k B B j)
      (h : (F j).comp dA.hom = dB.hom.comp (F i)) :
      UA.map dA ≫ L j = L i ≫ UB.map dB := by
    apply ModuleCat.hom_ext
    ext x
    change ULift.up (F j (dA.hom x.down)) = ULift.up (dB.hom (F i x.down))
    exact congrArg ULift.up (DFunLike.congr_fun h x.down)
  refine HomologicalComplex₂.homMk (fun pq => L pq.2) ?_ ?_
  · intro p p' q hpp
    change p' + 1 = p at hpp
    subst p
    let dA : chainLevel k A A q ⟶ chainLevel k A A q :=
      if Even p' then 𝟙 _ - cyclicMap k A q else normMap k A q
    let dB : chainLevel k B B q ⟶ chainLevel k B B q :=
      if Even p' then 𝟙 _ - cyclicMap k B q else normMap k B q
    have hA : ((cyclicBicomplex k A).d (p' + 1) p').f q = dA :=
      cyclicBicomplex_horizontal k A p' q
    have hB : ((cyclicBicomplex k B).d (p' + 1) p').f q = dB :=
      cyclicBicomplex_horizontal k B p' q
    have h : (F q).comp dA.hom = dB.hom.comp (F q) := by
      apply LinearMap.ext
      intro x
      by_cases hp : Even p'
      · simp only [dA, dB, if_pos hp]
        change F q ((𝟙 _ - cyclicMap k A q).hom x) =
          (𝟙 _ - cyclicMap k B q).hom (F q x)
        simp only [ModuleCat.hom_sub, ModuleCat.hom_id, LinearMap.sub_apply,
          LinearMap.id_apply, map_sub]
        exact congrArg (fun z => F q x - z)
          (DFunLike.congr_fun (TensorPower.consCyclicOperator_natural (f : A →ₗ[k] B) q) x)
      · simp only [dA, dB, if_neg hp]
        change F q ((normMap k A q).hom x) = (normMap k B q).hom (F q x)
        exact TensorPower.consNorm_natural (f : A →ₗ[k] B) q x
    change L q ≫ UB.map (((cyclicBicomplex k B).d (p' + 1) p').f q) =
      UA.map (((cyclicBicomplex k A).d (p' + 1) p').f q) ≫ L q
    exact (congrArg (fun d => L q ≫ UB.map d) hB).trans
      ((transport dA dB h).symm.trans
        (congrArg (fun d => UA.map d ≫ L q) hA).symm)
  · intro p q q' hqq
    change q' + 1 = q at hqq
    subst q
    let dA : chainLevel k A A (q' + 1) ⟶ chainLevel k A A q' :=
      if Even p then (bComplex k A).d (q' + 1) q' else (bPrimeComplex k A).d (q' + 1) q'
    let dB : chainLevel k B B (q' + 1) ⟶ chainLevel k B B q' :=
      if Even p then (bComplex k B).d (q' + 1) q' else (bPrimeComplex k B).d (q' + 1) q'
    have h : (F q').comp dA.hom = dB.hom.comp (F (q' + 1)) := by
      let dA₀ : chainLevel k A A (q' + 1) ⟶ chainLevel k A A q' :=
        (bComplex k A).d (q' + 1) q'
      let dA₁ : chainLevel k A A (q' + 1) ⟶ chainLevel k A A q' :=
        (bPrimeComplex k A).d (q' + 1) q'
      let dB₀ : chainLevel k B B (q' + 1) ⟶ chainLevel k B B q' :=
        (bComplex k B).d (q' + 1) q'
      let dB₁ : chainLevel k B B (q' + 1) ⟶ chainLevel k B B q' :=
        (bPrimeComplex k B).d (q' + 1) q'
      have hA : dA = if Even p then dA₀ else dA₁ := rfl
      have hB : dB = if Even p then dB₀ else dB₁ := rfl
      by_cases hp : Even p
      · have hA₀ : dA = dA₀ := hA.trans (if_pos hp)
        have hB₀ : dB = dB₀ := hB.trans (if_pos hp)
        exact ((congrArg (fun d : chainLevel k A A (q' + 1) ⟶ chainLevel k A A q' =>
          (F q').comp d.hom) hA₀).trans (bComplex_d_natural f q')).trans
            (congrArg (fun d : chainLevel k B B (q' + 1) ⟶ chainLevel k B B q' =>
              d.hom.comp (F (q' + 1))) hB₀.symm)
      · have hA₁ : dA = dA₁ := hA.trans (if_neg hp)
        have hB₁ : dB = dB₁ := hB.trans (if_neg hp)
        exact ((congrArg (fun d : chainLevel k A A (q' + 1) ⟶ chainLevel k A A q' =>
          (F q').comp d.hom) hA₁).trans (bPrimeComplex_d_natural f q')).trans
            (congrArg (fun d : chainLevel k B B (q' + 1) ⟶ chainLevel k B B q' =>
              d.hom.comp (F (q' + 1))) hB₁.symm)
    change L (q' + 1) ≫ UB.map dB = UA.map dA ≫ L q'
    exact (transport dA dB h).symm

/-- Every lifted bicomplex component is the native lifted original level map. -/
@[simp]
theorem cyclicBicomplexMap_f_f (f : A →ₙₐ[k] B) (p q : ℕ) :
    ((cyclicBicomplexMap f).f p).f q = levelMapLift (f : A →ₗ[k] B) q := rfl

omit [IsScalarTower k A A] [SMulCommClass k A A] in
/-- The native lifted level map preserves the identity. -/
theorem levelMapLift_id (n : ℕ) :
    levelMapLift (LinearMap.id : A →ₗ[k] A) n =
      𝟙 ((ModuleCat.uliftFunctor.{v, max u v} k).obj (chainLevel k A A n)) := by
  apply ModuleCat.hom_ext
  ext x
  rcases x with ⟨x⟩
  change ULift.up (TensorPower.consLevelMap (LinearMap.id : A →ₗ[k] A) n x) = ULift.up x
  simp only [TensorPower.consLevelMap_id, LinearMap.id_apply]

/-- The lifted bicomplex map of the identity algebra map is the identity. -/
theorem cyclicBicomplexMap_id :
    cyclicBicomplexMap (NonUnitalAlgHom.id k A) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  change levelMapLift (LinearMap.id : A →ₗ[k] A) q = 𝟙 _
  exact levelMapLift_id q

end Naturality

section Homology

/-- Cyclic homology is the homology of the cyclic total. -/
def cyclicHomology (n : ℕ) : ModuleCat.{max u v} k := (cyclicTotal k A).homology n

/-- The Connes complex is the native cokernel of the first horizontal column map. -/
def connesComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  HomologicalComplex₂.firstColumnCokernel (cyclicBicomplex k A)

/-- The homology of the Connes quotient complex. -/
def connesHomology (n : ℕ) : ModuleCat.{max u v} k := (connesComplex k A).homology n

/-- The cyclic total has its canonical projection to the Connes quotient. -/
def cyclicToConnes : cyclicTotal k A ⟶ connesComplex k A :=
  HomologicalComplex₂.firstColumnCokernelProjection (cyclicBicomplex k A)

/-- The first-column summand uses the original cokernel projection. -/
theorem cyclicToConnes_ι_zero (n : ℕ) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 n n (Nat.zero_add n) ≫
        (cyclicToConnes k A).f n =
      (cokernel.π ((cyclicBicomplex k A).d 1 0)).f n :=
  HomologicalComplex₂.ι_firstColumnCokernelProjectionX_zero (cyclicBicomplex k A) n

/-- Every later column is sent to zero by the canonical Connes projection. -/
theorem cyclicToConnes_ι_succ (p q n : ℕ) (h : p + 1 + q = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫
      (cyclicToConnes k A).f n = 0 :=
  HomologicalComplex₂.ι_firstColumnCokernelProjectionX_succ (cyclicBicomplex k A) p q n h

/-- The prescribed projection induces the map on native homology. -/
def cyclicToConnesHomology (n : ℕ) : cyclicHomology k A n ⟶ connesHomology k A n :=
  HomologicalComplex.homologyMap (cyclicToConnes k A) n

/-- Native evaluation identifies a Connes term with the cokernel of its level map. -/
def connesComplexXIsoCokernel (n : ℕ) :
    (connesComplex k A).X n ≅ cokernel (((cyclicBicomplex k A).d 1 0).f n) :=
  (asIso (cokernelComparison ((cyclicBicomplex k A).d 1 0)
    (HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n))).symm

/-- The evaluated incoming map is exactly the original signed endomorphism 1-t. -/
theorem connesComplex_levelMap (n : ℕ) :
    (((cyclicBicomplex k A).d 1 0).f n).hom =
      (1 : Module.End k (A ⊗[k] TensorPower k n A)) -
        TensorPower.consCyclicOperator k A n := by
  change @Eq (Module.End k (A ⊗[k] TensorPower k n A))
    (((cyclicBicomplex k A).d 1 0).f n).hom
    ((1 : Module.End k (A ⊗[k] TensorPower k n A)) -
      TensorPower.consCyclicOperator k A n)
  dsimp only [cyclicBicomplex]
  erw [ChainComplex.of_d]
  change @Eq (Module.End k (A ⊗[k] TensorPower k n A))
    ((if Even (0 : ℕ) then 𝟙 (chainLevel k A A n) - cyclicMap k A n
      else normMap k A n).hom)
    ((1 : Module.End k (A ⊗[k] TensorPower k n A)) -
      TensorPower.consCyclicOperator k A n)
  erw [ite_eq_left (show Even (0 : ℕ) from ⟨0, rfl⟩)]
  rfl

/-- The native evaluated cokernel has its original module range-quotient coordinates. -/
def connesComplexXIsoRangeQuotient (n : ℕ) :
    (connesComplex k A).X n ≅
      ModuleCat.of k (chainLevel k A A n ⧸
        LinearMap.range (((cyclicBicomplex k A).d 1 0).f n).hom) :=
  connesComplexXIsoCokernel k A n ≪≫
    ModuleCat.cokernelIsoRangeQuotient (((cyclicBicomplex k A).d 1 0).f n)

/-- The native range-quotient coordinates retain the original cokernel representative. -/
theorem connesComplex_X_isoRangeQuotient_π (n : ℕ) :
    (cokernel.π ((cyclicBicomplex k A).d 1 0)).f n ≫
      (connesComplexXIsoRangeQuotient k A n).hom =
        ModuleCat.ofHom (LinearMap.range (((cyclicBicomplex k A).d 1 0).f n).hom).mkQ := by
  let D : HomologicalComplex₂ (ModuleCat.{max u v} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  let P : ChainComplex (ModuleCat.{max u v} k) ℕ := D.X 1
  let Q : ChainComplex (ModuleCat.{max u v} k) ℕ := D.X 0
  let f : P ⟶ Q := D.d 1 0
  let E : ChainComplex (ModuleCat.{max u v} k) ℕ ⥤ ModuleCat.{max u v} k :=
    HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n
  let g : E.obj P ⟶ E.obj Q := E.map f
  let e : cokernel g ≅ E.obj (cokernel f) := asIso (cokernelComparison f E)
  let p : E.obj Q ⟶ cokernel g := cokernel.π g
  let q : E.obj Q ⟶ E.obj (cokernel f) := E.map (cokernel.π f)
  let z := ModuleCat.cokernelIsoRangeQuotient g
  have h : p ≫ e.hom = q := π_comp_cokernelComparison f E
  have hp : q ≫ e.inv = p := by
    calc
      _ = (p ≫ e.hom) ≫ e.inv :=
        congrArg (fun a : E.obj Q ⟶ E.obj (cokernel f) => a ≫ e.inv) h.symm
      _ = p ≫ (e.hom ≫ e.inv) := Category.assoc _ _ _
      _ = p ≫ 𝟙 (cokernel g) :=
        congrArg (fun a : cokernel g ⟶ cokernel g => p ≫ a) e.hom_inv_id
      _ = p := Category.comp_id p
  change q ≫ (e.inv ≫ z.hom) = _
  calc
    _ = (q ≫ e.inv) ≫ z.hom := (Category.assoc _ _ _).symm
    _ = p ≫ z.hom :=
      congrArg (fun a : E.obj Q ⟶ cokernel g => a ≫ z.hom) hp
    _ = _ := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom g

/-- The Connes term is the coinvariant module of the signed cyclic action. -/
def connesComplexXIsoCoinvariants (n : ℕ) :
    (connesComplex k A).X n ≅
      ModuleCat.of k (TensorPower.consCyclicRepresentation k A n).Coinvariants := by
  let ρ := TensorPower.consCyclicRepresentation k A n
  let g := Multiplicative.ofAdd (1 : ZMod (n + 1))
  have hg : ∀ z, z ∈ Subgroup.zpowers g := by
    intro z
    refine Subgroup.mem_zpowers_iff.mpr ⟨((Multiplicative.toAdd z).val : ℤ), ?_⟩
    change Multiplicative.ofAdd (1 : ZMod (n + 1)) ^
      ((Multiplicative.toAdd z).val : ℤ) = Multiplicative.ofAdd (Multiplicative.toAdd z)
    rw [← ofAdd_zsmul]
    apply congrArg Multiplicative.ofAdd
    simp only [zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hr : LinearMap.range (ρ g - LinearMap.id) =
      LinearMap.range (((cyclicBicomplex k A).d 1 0).f n).hom := by
    have hIncoming : (((cyclicBicomplex k A).d 1 0).f n).hom =
        (LinearMap.id : Module.End k (chainLevel k A A n)) -
          TensorPower.consCyclicOperator k A n := connesComplex_levelMap k A n
    have hRight : LinearMap.range (((cyclicBicomplex k A).d 1 0).f n).hom =
        LinearMap.range ((LinearMap.id : Module.End k (chainLevel k A A n)) -
          TensorPower.consCyclicOperator k A n) :=
      congrArg (fun f : Module.End k (chainLevel k A A n) => LinearMap.range f) hIncoming
    have hLeft : LinearMap.range (ρ g - LinearMap.id) =
        LinearMap.range ((LinearMap.id : Module.End k (chainLevel k A A n)) -
          TensorPower.consCyclicOperator k A n) := by
      dsimp only [ρ, g]
      rw [TensorPower.consCyclicRepresentation_generator]
      rw [show TensorPower.consCyclicOperator k A n -
          (LinearMap.id : Module.End k (chainLevel k A A n)) =
        -((LinearMap.id : Module.End k (chainLevel k A A n)) -
          TensorPower.consCyclicOperator k A n) by simp only [neg_sub]]
      exact LinearMap.range_neg _
    exact hLeft.trans hRight.symm
  exact connesComplexXIsoRangeQuotient k A n ≪≫
    (Submodule.quotEquivOfEq _ _ hr.symm).toModuleIso ≪≫
      (Representation.FiniteCyclicGroup.coinvariantsEquiv ρ g hg).symm.toModuleIso

section OrdinaryMaps

variable {k A} {B : Type v} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Full faithfulness lowers the computed lifted map to the original common-category bicomplex. -/
def cyclicBicomplexHom (f : A →ₙₐ[k] B) : cyclicBicomplex k A ⟶ cyclicBicomplex k B :=
  (((ModuleCat.uliftFunctor.{v, max u v} k).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).preimage
      (cyclicBicomplexMap f)

/-- Every original bicomplex component is the tensor map of the nonunital map. -/
theorem cyclicBicomplexHom_f_f (f : A →ₙₐ[k] B) (p q : ℕ) :
    ((cyclicBicomplexHom f).f p).f q =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q) := by
  let U := ModuleCat.uliftFunctor.{v, max u v} k
  let V := (U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)
  have h := congrArg
    (fun m : V.obj (cyclicBicomplex k A) ⟶ V.obj (cyclicBicomplex k B) => (m.f p).f q)
    (V.map_preimage (cyclicBicomplexMap f))
  apply U.map_injective
  change U.map (((cyclicBicomplexHom f).f p).f q) =
    U.map (ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) q))
  change U.map (((cyclicBicomplexHom f).f p).f q) =
    ((cyclicBicomplexMap f).f p).f q at h
  exact h.trans (cyclicBicomplexMap_f_f f p q)

variable {D : Type v} [NonUnitalRing D] [Module k D]
  [IsScalarTower k D D] [SMulCommClass k D D]

/-- The original bicomplex map preserves identity nonunital maps. -/
theorem cyclicBicomplexHom_id :
    cyclicBicomplexHom (NonUnitalAlgHom.id k A) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  rw [cyclicBicomplexHom_f_f, HomologicalComplex.id_f, HomologicalComplex.id_f]
  apply ModuleCat.hom_ext
  change TensorPower.consLevelMap (LinearMap.id : A →ₗ[k] A) q = LinearMap.id
  exact TensorPower.consLevelMap_id q

/-- The original bicomplex map preserves composition in the given order. -/
theorem cyclicBicomplexHom_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) :
    cyclicBicomplexHom (g.comp f) = cyclicBicomplexHom f ≫ cyclicBicomplexHom g := by
  apply HomologicalComplex.hom_ext
  intro p
  apply HomologicalComplex.hom_ext
  intro q
  rw [cyclicBicomplexHom_f_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cyclicBicomplexHom_f_f, cyclicBicomplexHom_f_f]
  apply ModuleCat.hom_ext
  change TensorPower.consLevelMap ((g : B →ₗ[k] D).comp (f : A →ₗ[k] B)) q =
    (TensorPower.consLevelMap (g : B →ₗ[k] D) q).comp
      (TensorPower.consLevelMap (f : A →ₗ[k] B) q)
  exact (TensorPower.consLevelMap_comp (f : A →ₗ[k] B) (g : B →ₗ[k] D) q).symm

/-- The original total-complex map of a nonunital algebra map. -/
def cyclicTotalHom (f : A →ₙₐ[k] B) : cyclicTotal k A ⟶ cyclicTotal k B :=
  HomologicalComplex₂.total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ)

/-- Native homology gives the cyclic-homology map in a common module category. -/
def cyclicHomologyMap (f : A →ₙₐ[k] B) (n : ℕ) : cyclicHomology k A n ⟶ cyclicHomology k B n :=
  HomologicalComplex.homologyMap (cyclicTotalHom f) n

/-- The original bicomplex map induces the native Connes-cokernel map. -/
def connesComplexHom (f : A →ₙₐ[k] B) : connesComplex k A ⟶ connesComplex k B :=
  HomologicalComplex₂.firstColumnCokernelMap (cyclicBicomplexHom f)

/-- The Connes homology map is native homology of the cokernel map. -/
def connesHomologyMap (f : A →ₙₐ[k] B) (n : ℕ) : connesHomology k A n ⟶ connesHomology k B n :=
  HomologicalComplex.homologyMap (connesComplexHom f) n

/-- The prescribed total-to-quotient map is natural for nonunital maps. -/
theorem cyclicToConnes_naturality (f : A →ₙₐ[k] B) :
    cyclicTotalHom f ≫ cyclicToConnes k B = cyclicToConnes k A ≫ connesComplexHom f :=
  HomologicalComplex₂.firstColumnCokernelProjection_naturality (cyclicBicomplexHom f)

/-- The homology comparison is natural for those same nonunital maps. -/
theorem cyclicToConnesHomology_naturality (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomologyMap f n ≫ cyclicToConnesHomology k B n =
      cyclicToConnesHomology k A n ≫ connesHomologyMap f n := by
  have h := congrArg
    (fun m : cyclicTotal k A ⟶ connesComplex k B => HomologicalComplex.homologyMap m n)
    (cyclicToConnes_naturality f)
  change HomologicalComplex.homologyMap (cyclicTotalHom f) n ≫
      HomologicalComplex.homologyMap (cyclicToConnes k B) n =
    HomologicalComplex.homologyMap (cyclicToConnes k A) n ≫
      HomologicalComplex.homologyMap (connesComplexHom f) n
  simpa only [HomologicalComplex.homologyMap_comp] using h

/-- Native totalization and homology preserve the identity algebra map. -/
theorem cyclicHomologyMap_id (n : ℕ) :
    cyclicHomologyMap (NonUnitalAlgHom.id k A) n = 𝟙 (cyclicHomology k A n) := by
  have hTotal : cyclicTotalHom (NonUnitalAlgHom.id k A) = 𝟙 (cyclicTotal k A) := by
    change HomologicalComplex₂.total.map
        (cyclicBicomplexHom (NonUnitalAlgHom.id k A)) (ComplexShape.down ℕ) =
      𝟙 ((cyclicBicomplex k A).total (ComplexShape.down ℕ))
    rw [cyclicBicomplexHom_id]
    exact HomologicalComplex₂.total.map_id (cyclicBicomplex k A) (ComplexShape.down ℕ)
  change HomologicalComplex.homologyMap (cyclicTotalHom (NonUnitalAlgHom.id k A)) n =
    𝟙 ((cyclicTotal k A).homology n)
  rw [hTotal]
  exact HomologicalComplex.homologyMap_id (cyclicTotal k A) n

/-- The homology maps preserve the ordered composition of nonunital maps. -/
theorem cyclicHomologyMap_comp (f : A →ₙₐ[k] B) (g : B →ₙₐ[k] D) (n : ℕ) :
    cyclicHomologyMap (g.comp f) n = cyclicHomologyMap f n ≫ cyclicHomologyMap g n := by
  have hTotal : cyclicTotalHom (g.comp f) = cyclicTotalHom f ≫ cyclicTotalHom g := by
    change HomologicalComplex₂.total.map (cyclicBicomplexHom (g.comp f))
        (ComplexShape.down ℕ) =
      HomologicalComplex₂.total.map (cyclicBicomplexHom f) (ComplexShape.down ℕ) ≫
        HomologicalComplex₂.total.map (cyclicBicomplexHom g) (ComplexShape.down ℕ)
    rw [cyclicBicomplexHom_comp]
    exact HomologicalComplex₂.total.map_comp
      (cyclicBicomplexHom f) (cyclicBicomplexHom g) (ComplexShape.down ℕ)
  change HomologicalComplex.homologyMap (cyclicTotalHom (g.comp f)) n =
    HomologicalComplex.homologyMap (cyclicTotalHom f) n ≫
      HomologicalComplex.homologyMap (cyclicTotalHom g) n
  rw [hTotal]
  exact HomologicalComplex.homologyMap_comp (cyclicTotalHom f) (cyclicTotalHom g) n

end OrdinaryMaps

/-- Native exact ULifting and the diagonal total comparison identify lifted homology. -/
def cyclicHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) (A : Type algebra) [CommRing k] [NonUnitalRing A]
    [Module k A] [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj (cyclicHomology k A n) ≅
      (HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (cyclicBicomplex k A)) (ComplexShape.down ℕ)).homology n := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  letI : ∀ m, PreservesColimit
      (Discrete.functor ((cyclicBicomplex k A).toGradedObject.mapObjFun
        (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  let e := HomologicalComplex₂.functorTotalIso U (cyclicBicomplex k A)
  let h :
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicTotal k A)).homology n ≅
        U.obj (cyclicHomology k A n) :=
    ((cyclicTotal k A).sc n).mapHomologyIso U
  exact h.symm ≪≫ HomologicalComplex.homologyMapIso e n

section IndependentMaps

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- The lift comparisons yield an homology linear map across independent worlds. -/
def cyclicHomologyLinearMap (f : A →ₙₐ[k] B) (n : ℕ) :
    cyclicHomology k A n →ₗ[k] cyclicHomology k B n := by
  let eA := cyclicHomologyLiftIso.{w} k A n
  let eB := cyclicHomologyLiftIso.{v} k B n
  let φ := HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)
  let m := eA.hom ≫ HomologicalComplex.homologyMap φ n ≫ eB.inv
  exact ULift.moduleEquiv.toLinearMap.comp
    (m.hom.comp ULift.moduleEquiv.symm.toLinearMap)

/-- The original-carrier map is characterized by the computed common-world homology map. -/
theorem cyclicHomologyLinearMap_lift (f : A →ₙₐ[k] B) (n : ℕ)
    (z : cyclicHomology k A n) :
    (cyclicHomologyLiftIso.{v} k B n).hom (ULift.up (cyclicHomologyLinearMap f n z)) =
      HomologicalComplex.homologyMap
        (HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)) n
        ((cyclicHomologyLiftIso.{w} k A n).hom (ULift.up z)) := by
  let eA := cyclicHomologyLiftIso.{w} k A n
  let eB := cyclicHomologyLiftIso.{v} k B n
  let φ := HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)
  change eB.hom (eB.inv (HomologicalComplex.homologyMap φ n (eA.hom (ULift.up z)))) =
    HomologicalComplex.homologyMap φ n (eA.hom (ULift.up z))
  exact ModuleCat.hom_inv_apply eB _

end IndependentMaps

end Homology

end Multiplication

end ModuleCat.Algebra.Hochschild.NonUnital

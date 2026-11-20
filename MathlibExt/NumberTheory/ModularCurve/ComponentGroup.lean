/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_ComponentGroup.lean`
and
`Definitions/Def_ModularCurve_CharacterLatticePairings.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of
the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Defs

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Ring

@[expose] public section

namespace ModularCurve

open Finset

section CharacterLattice

variable {ι : Type*} [Fintype ι]

/-- The degree of an integer-valued function on a finite type: the sum of
its values. -/
def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

@[simp] theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

/-- The degree-zero character lattice: the kernel of the degree map. -/
def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

/-- Membership in the character lattice is vanishing of the degree. -/
theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing

variable {ι : Type*} [Fintype ι]

/-- The width pairing on integer-valued functions, weighted by `e`. -/
def widthPairing (e : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) := by
  simp only [widthPairing, LinearMap.mk₂_apply]

/-- The width pairing is symmetric. -/
theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The Gram map of the width pairing, restricted to the character
lattice. -/
def gramMap (e : ι → ℕ) :
    characterLattice ι →ₗ[ℤ] Module.Dual ℤ (characterLattice ι) :=
  (widthPairing e).domRestrict₁₂ (characterLattice ι) (characterLattice ι)

@[simp] theorem gramMap_apply (e : ι → ℕ) (D D' : characterLattice ι) :
    gramMap e D D' = ∑ x : ι, (e x : ℤ) * (D.1 x * D'.1 x) := by
  simp only [gramMap, LinearMap.domRestrict₁₂_apply, widthPairing_apply]

/-- The component group: the cokernel of the Gram map, presented as the
quotient of the dual lattice by the range of the Gram map. -/
abbrev componentGroup (e : ι → ℕ) :=
  Module.Dual ℤ (characterLattice ι) ⧸ LinearMap.range (gramMap e)

/-- The projection from the dual lattice to the component group. -/
abbrev componentGroupProj (e : ι → ℕ) :
    Module.Dual ℤ (characterLattice ι) →ₗ[ℤ] componentGroup e :=
  (LinearMap.range (gramMap e)).mkQ

end Pairing

variable (S : Type*) [Fintype S]

/-- The degree of a single-supported function is its supported value. -/
theorem degreeOn_single [DecidableEq S] (s : S) (n : ℤ) :
    degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

/-- The degree of a constant function. -/
theorem degreeOn_const (n : ℤ) :
    degreeOn S (fun _ => n) = Fintype.card S • n := by
  simp [degreeOn_apply]

variable {S}

/-- A difference of two unit single-supported functions lies in the
character lattice. -/
theorem single_sub_single_mem [DecidableEq S] (s t : S) :
    Pi.single s (1 : ℤ) - Pi.single t 1 ∈ characterLattice S := by
  rw [characterLattice, LinearMap.mem_ker, map_sub, degreeOn_single,
    degreeOn_single, sub_self]

namespace CharacterLattice

section MultiplicativePairing

variable {G : Type*} [CommGroup G]

/-- Raising to a summed integer exponent is the product of the powers. -/
theorem zpow_finset_sum {ι : Type*} (g : G) (e : ι → ℤ) (t : Finset ι) :
    g ^ (∑ i ∈ t, e i) = ∏ i ∈ t, g ^ e i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

/-- The monomial attached to an exponent function `a` and weights `w`. -/
def zpowProd (a : S → ℤ) (w : S → G) : G := ∏ s, w s ^ a s

@[simp]
theorem zpowProd_def (a : S → ℤ) (w : S → G) :
    zpowProd a w = ∏ s, w s ^ a s :=
  rfl

/-- The monomial is additive in the exponent function. -/
theorem zpowProd_add (a b : S → ℤ) (w : S → G) :
    zpowProd (a + b) w = zpowProd a w * zpowProd b w := by
  simp [zpowProd, zpow_add, Finset.prod_mul_distrib]

/-- The monomial at the zero exponent is `1`. -/
theorem zpowProd_zero_left (w : S → G) : zpowProd (0 : S → ℤ) w = 1 := by
  simp [zpowProd]

/-- Negating the exponent inverts the monomial. -/
theorem zpowProd_neg (a : S → ℤ) (w : S → G) :
    zpowProd (-a) w = (zpowProd a w)⁻¹ := by
  simp [zpowProd, Finset.prod_inv_distrib]

/-- The monomial is multiplicative in the weights. -/
theorem zpowProd_mul (a : S → ℤ) (w w' : S → G) :
    zpowProd a (w * w') = zpowProd a w * zpowProd a w' := by
  simp [zpowProd, mul_zpow, Finset.prod_mul_distrib]

/-- The monomial at the constant weight `1` is `1`. -/
theorem zpowProd_one_right (a : S → ℤ) : zpowProd a (1 : S → G) = 1 := by
  simp [zpowProd]

/-- The monomial at a constant weight is a power by the degree. -/
theorem zpowProd_const (a : S → ℤ) (c : G) :
    zpowProd a (fun _ => c) = c ^ degreeOn S a := by
  rw [zpowProd_def, degreeOn_apply, zpow_finset_sum]

/-- On the character lattice, the monomial at a constant weight is `1`. -/
theorem zpowProd_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S)
    (c : G) : zpowProd a (fun _ => c) = 1 := by
  rw [zpowProd_const, show degreeOn S a = 0 from ha, zpow_zero]

/-- The monomial as a monoid homomorphism in the weights. -/
def zpowProdHom (a : S → ℤ) : (S → G) →* G where
  toFun := zpowProd a
  map_one' := zpowProd_one_right a
  map_mul' := zpowProd_mul a

@[simp]
theorem zpowProdHom_apply (a : S → ℤ) (w : S → G) :
    zpowProdHom a w = zpowProd a w :=
  rfl

/-- Evaluation of a character (an element of the character lattice)
at weights `w`. -/
def evalHom (a : characterLattice S) : (S → G) →* G := zpowProdHom (a : S → ℤ)

@[simp]
theorem evalHom_apply (a : characterLattice S) (w : S → G) :
    evalHom a w = ∏ s, w s ^ (a : S → ℤ) s :=
  rfl

/-- A character evaluated at a constant weight is `1`. -/
theorem evalHom_const (a : characterLattice S) (c : G) :
    evalHom a (fun _ => c) = 1 :=
  zpowProd_const_of_mem a.2 c

/-- Evaluation is additive in the character. -/
theorem evalHom_add (a b : characterLattice S) (w : S → G) :
    evalHom (a + b) w = evalHom a w * evalHom b w :=
  zpowProd_add _ _ w

end MultiplicativePairing

section AdditivePairing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The additive pairing: the `a`-weighted sum of module elements. -/
def smulSum (a : S → ℤ) (v : S → M) : M := ∑ s, a s • v s

@[simp]
theorem smulSum_def (a : S → ℤ) (v : S → M) :
    smulSum a v = ∑ s, a s • v s :=
  rfl

/-- The additive pairing is additive in the exponent function. -/
theorem smulSum_add_left (a b : S → ℤ) (v : S → M) :
    smulSum (a + b) v = smulSum a v + smulSum b v := by
  simp [smulSum, add_smul, Finset.sum_add_distrib]

/-- The additive pairing is additive in the module-valued function. -/
theorem smulSum_add_right (a : S → ℤ) (v v' : S → M) :
    smulSum a (v + v') = smulSum a v + smulSum a v' := by
  simp [smulSum, smul_add, Finset.sum_add_distrib]

/-- The additive pairing commutes with scalar multiplication. -/
theorem smulSum_smul_right (a : S → ℤ) (r : R) (v : S → M) :
    smulSum a (r • v) = r • smulSum a v := by
  simp only [smulSum_def, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

/-- The additive pairing at a constant value is a degree multiple. -/
theorem smulSum_const (a : S → ℤ) (m : M) :
    smulSum a (fun _ => m) = degreeOn S a • m := by
  simp [smulSum, degreeOn_apply, Finset.sum_smul]

/-- On the character lattice, the additive pairing at a constant
value vanishes. -/
theorem smulSum_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S)
    (m : M) : smulSum a (fun _ => m) = 0 := by
  rw [smulSum_const, show degreeOn S a = 0 from ha, zero_smul]

end AdditivePairing

section Functoriality

variable {S' : Type*} [Fintype S']

/-- A linear map scales all degrees by a fixed factor `d`. -/
def IsDegreeScaling (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) : Prop :=
  ∀ a, degreeOn S' (f a) = d * degreeOn S a

/-- A degree-scaling map preserves the character lattices. -/
theorem IsDegreeScaling.map_mem {f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)} {d : ℤ}
    (hf : IsDegreeScaling f d) {a : S → ℤ} (ha : a ∈ characterLattice S) :
    f a ∈ characterLattice S' := by
  rw [characterLattice, LinearMap.mem_ker, hf a,
    show degreeOn S a = 0 from ha, mul_zero]

/-- Restriction of a degree-scaling map to the character lattices. -/
def restrictDegZero (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ)
    (hf : IsDegreeScaling f d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  f.restrict fun _ ha => hf.map_mem ha

@[simp]
theorem coe_restrictDegZero_apply (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ)
    (hf : IsDegreeScaling f d) (a : characterLattice S) :
    (restrictDegZero f d hf a : S' → ℤ) = f a :=
  rfl

omit [Fintype S] [Fintype S'] in
/-- Pullback of integer-valued functions along an equivalence. -/
def permMapFun (σ : S ≃ S') : (S → ℤ) →ₗ[ℤ] (S' → ℤ) :=
  LinearMap.funLeft ℤ ℤ σ.symm

omit [Fintype S] [Fintype S'] in
@[simp]
theorem permMapFun_apply (σ : S ≃ S') (a : S → ℤ) (s' : S') :
    permMapFun σ a s' = a (σ.symm s') :=
  rfl

/-- Pullback along an equivalence preserves degrees. -/
theorem isDegreeScaling_permMapFun (σ : S ≃ S') :
    IsDegreeScaling (permMapFun σ) 1 := by
  intro a
  simp only [degreeOn_apply, permMapFun_apply, one_mul]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

/-- The map on character lattices induced by an equivalence. -/
def permMap (σ : S ≃ S') :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (permMapFun σ) 1 (isDegreeScaling_permMapFun σ)

@[simp]
theorem coe_permMap_apply (σ : S ≃ S') (a : characterLattice S) (s' : S') :
    (permMap σ a : S' → ℤ) s' = (a : S → ℤ) (σ.symm s') :=
  rfl

omit [Fintype S'] in
/-- The linear map on integer-valued functions given by a correspondence
matrix `B`. -/
def corrMapFun (B : S → S' → ℤ) : (S → ℤ) →ₗ[ℤ] (S' → ℤ) where
  toFun a s' := ∑ s, a s * B s s'
  map_add' a b := by ext s'; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext s'; simp [Finset.mul_sum, mul_assoc]

omit [Fintype S'] in
@[simp]
theorem corrMapFun_apply (B : S → S' → ℤ) (a : S → ℤ) (s' : S') :
    corrMapFun B a s' = ∑ s, a s * B s s' :=
  rfl

/-- A correspondence whose rows all sum to `d` scales degrees by `d`. -/
theorem isDegreeScaling_corrMapFun (B : S → S' → ℤ) (d : ℤ)
    (hB : ∀ s, ∑ s', B s s' = d) : IsDegreeScaling (corrMapFun B) d := by
  intro a
  simp only [degreeOn_apply, corrMapFun_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, hB s, mul_comm]

/-- The map on character lattices induced by a correspondence. -/
def corrMap (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (corrMapFun B) d (isDegreeScaling_corrMapFun B d hB)

@[simp]
theorem coe_corrMap_apply (B : S → S' → ℤ) (d : ℤ)
    (hB : ∀ s, ∑ s', B s s' = d) (a : characterLattice S) (s' : S') :
    (corrMap B d hB a : S' → ℤ) s' = ∑ s, (a : S → ℤ) s * B s s' :=
  rfl

/-- Monomials are compatible with pullback along an equivalence. -/
theorem zpowProd_permMapFun {G : Type*} [CommGroup G] (σ : S ≃ S')
    (a : S → ℤ) (w : S' → G) :
    zpowProd (permMapFun σ a) w = zpowProd a (w ∘ σ) := by
  simp only [zpowProd, permMapFun_apply, Function.comp_apply]
  exact Fintype.prod_equiv σ.symm _ _ fun _ => by simp

/-- Monomials are compatible with a correspondence map. -/
theorem zpowProd_corrMapFun {G : Type*} [CommGroup G] (B : S → S' → ℤ)
    (a : S → ℤ) (w : S' → G) :
    zpowProd (corrMapFun B a) w =
      zpowProd a (fun s => ∏ s', w s' ^ B s s') := by
  simp only [zpowProd_def, corrMapFun_apply]
  calc (∏ s', w s' ^ ∑ s, a s * B s s')
      = ∏ s', ∏ s, w s' ^ (a s * B s s') :=
          Finset.prod_congr rfl fun s' _ => zpow_finset_sum (w s') _ _
    _ = ∏ s, ∏ s', w s' ^ (a s * B s s') := Finset.prod_comm
    _ = ∏ s, (∏ s', w s' ^ B s s') ^ a s := by
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [← Finset.prod_zpow]
          exact Finset.prod_congr rfl fun s' _ => by rw [zpow_mul']

end Functoriality

end CharacterLattice

end ModularCurve

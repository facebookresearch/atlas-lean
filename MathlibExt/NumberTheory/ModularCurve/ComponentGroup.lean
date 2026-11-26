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

/-- **Degree.** The degree of an integer-valued function on a finite type: the sum of its values. -/
def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

@[simp] theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

/-- **Character lattice.** The degree-zero character lattice: the kernel of the degree map. -/
def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

/-- **Membership in the character lattice.** A function lies in the character lattice exactly when
its values sum to zero. -/
theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing

variable {ι : Type*} [Fintype ι]

/-- **Width pairing.** The pairing `(D, D') ↦ ∑ x, e x * (D x * D' x)` on integer-valued functions,
weighted by the widths `e`. -/
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

/-- **Symmetry of the width pairing.** The width pairing is symmetric. -/
theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Gram map.** The Gram map of the width pairing, restricted to the character lattice. -/
def gramMap (e : ι → ℕ) :
    characterLattice ι →ₗ[ℤ] Module.Dual ℤ (characterLattice ι) :=
  (widthPairing e).domRestrict₁₂ (characterLattice ι) (characterLattice ι)

@[simp] theorem gramMap_apply (e : ι → ℕ) (D D' : characterLattice ι) :
    gramMap e D D' = ∑ x : ι, (e x : ℤ) * (D.1 x * D'.1 x) := by
  simp only [gramMap, LinearMap.domRestrict₁₂_apply, widthPairing_apply]

/-- **Cokernel of the Gram map.** The quotient of the dual lattice by the range of the Gram map.
This is the general cokernel, defined for all widths; the component group of a curve with toric
reduction is the case of positive widths. A zero width can make the cokernel infinite: for two
indices of width zero the Gram map vanishes and the cokernel is `ℤ`. -/
abbrev componentGroup (e : ι → ℕ) :=
  Module.Dual ℤ (characterLattice ι) ⧸ LinearMap.range (gramMap e)

/-- **Projection to the cokernel.** The projection from the dual lattice to the cokernel
`componentGroup e`. -/
abbrev componentGroupProj (e : ι → ℕ) :
    Module.Dual ℤ (characterLattice ι) →ₗ[ℤ] componentGroup e :=
  (LinearMap.range (gramMap e)).mkQ

end Pairing

variable (S : Type*) [Fintype S]

/-- **Degree of a single-supported function.** The degree of `Pi.single s n` is its supported value
`n`. -/
theorem degreeOn_single [DecidableEq S] (s : S) (n : ℤ) :
    degreeOn S (Pi.single s n) = n := by
  simp [degreeOn_apply]

/-- **Degree of a constant function.** The degree of the constant function `n` on `S` is
`Fintype.card S • n`. -/
theorem degreeOn_const (n : ℤ) :
    degreeOn S (fun _ => n) = Fintype.card S • n := by
  simp [degreeOn_apply]

variable {S}

/-- **Differences of unit functions.** A difference of two unit single-supported functions lies in
the character lattice. -/
theorem single_sub_single_mem [DecidableEq S] (s t : S) :
    Pi.single s (1 : ℤ) - Pi.single t 1 ∈ characterLattice S := by
  rw [characterLattice, LinearMap.mem_ker, map_sub, degreeOn_single,
    degreeOn_single, sub_self]

namespace CharacterLattice

section MultiplicativePairing

variable {G : Type*} [CommGroup G]

/-- **Power by a sum of exponents.** Raising to a summed integer exponent is the product of the
powers. -/
theorem zpow_finset_sum {ι : Type*} (g : G) (e : ι → ℤ) (t : Finset ι) :
    g ^ (∑ i ∈ t, e i) = ∏ i ∈ t, g ^ e i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

/-- **Monomial.** The monomial `∏ s, w s ^ a s` attached to an exponent function `a` and weights
`w`. -/
def zpowProd (a : S → ℤ) (w : S → G) : G := ∏ s, w s ^ a s

@[simp]
theorem zpowProd_def (a : S → ℤ) (w : S → G) :
    zpowProd a w = ∏ s, w s ^ a s :=
  rfl

/-- **Monomial of a sum of exponents.** The monomial is additive in the exponent function. -/
theorem zpowProd_add (a b : S → ℤ) (w : S → G) :
    zpowProd (a + b) w = zpowProd a w * zpowProd b w := by
  simp [zpowProd, zpow_add, Finset.prod_mul_distrib]

/-- **Monomial at the zero exponent.** The monomial at the zero exponent is `1`. -/
theorem zpowProd_zero_left (w : S → G) : zpowProd (0 : S → ℤ) w = 1 := by
  simp [zpowProd]

/-- **Monomial at a negated exponent.** Negating the exponent inverts the monomial. -/
theorem zpowProd_neg (a : S → ℤ) (w : S → G) :
    zpowProd (-a) w = (zpowProd a w)⁻¹ := by
  simp [zpowProd, Finset.prod_inv_distrib]

/-- **Monomial of a product of weights.** The monomial is multiplicative in the weights. -/
theorem zpowProd_mul (a : S → ℤ) (w w' : S → G) :
    zpowProd a (w * w') = zpowProd a w * zpowProd a w' := by
  simp [zpowProd, mul_zpow, Finset.prod_mul_distrib]

/-- **Monomial at unit weights.** The monomial at the constant weight `1` is `1`. -/
theorem zpowProd_one_right (a : S → ℤ) : zpowProd a (1 : S → G) = 1 := by
  simp [zpowProd]

/-- **Monomial at a constant weight.** The monomial at a constant weight is a power by the
degree. -/
theorem zpowProd_const (a : S → ℤ) (c : G) :
    zpowProd a (fun _ => c) = c ^ degreeOn S a := by
  rw [zpowProd_def, degreeOn_apply, zpow_finset_sum]

/-- **Monomial of a character at a constant weight.** On the character lattice, the monomial at a
constant weight is `1`. -/
theorem zpowProd_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S)
    (c : G) : zpowProd a (fun _ => c) = 1 := by
  rw [zpowProd_const, show degreeOn S a = 0 from ha, zpow_zero]

/-- **Monomial homomorphism.** The monomial as a monoid homomorphism in the weights. -/
def zpowProdHom (a : S → ℤ) : (S → G) →* G where
  toFun := zpowProd a
  map_one' := zpowProd_one_right a
  map_mul' := zpowProd_mul a

@[simp]
theorem zpowProdHom_apply (a : S → ℤ) (w : S → G) :
    zpowProdHom a w = zpowProd a w :=
  rfl

/-- **Evaluation of a character.** Evaluation of a character (an element of the character lattice)
at weights `w`. -/
def evalHom (a : characterLattice S) : (S → G) →* G := zpowProdHom (a : S → ℤ)

@[simp]
theorem evalHom_apply (a : characterLattice S) (w : S → G) :
    evalHom a w = ∏ s, w s ^ (a : S → ℤ) s :=
  rfl

/-- **Character at a constant weight.** A character evaluated at a constant weight is `1`. -/
theorem evalHom_const (a : characterLattice S) (c : G) :
    evalHom a (fun _ => c) = 1 :=
  zpowProd_const_of_mem a.2 c

/-- **Evaluation of a sum of characters.** Evaluation is additive in the character. -/
theorem evalHom_add (a b : characterLattice S) (w : S → G) :
    evalHom (a + b) w = evalHom a w * evalHom b w :=
  zpowProd_add _ _ w

end MultiplicativePairing

section AdditivePairing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- **Additive pairing.** The `a`-weighted sum `∑ s, a s • v s` of module elements. -/
def smulSum (a : S → ℤ) (v : S → M) : M := ∑ s, a s • v s

@[simp]
theorem smulSum_def (a : S → ℤ) (v : S → M) :
    smulSum a v = ∑ s, a s • v s :=
  rfl

/-- **Additive pairing of a sum of exponents.** The additive pairing is additive in the exponent
function. -/
theorem smulSum_add_left (a b : S → ℤ) (v : S → M) :
    smulSum (a + b) v = smulSum a v + smulSum b v := by
  simp [smulSum, add_smul, Finset.sum_add_distrib]

/-- **Additive pairing of a sum of values.** The additive pairing is additive in the module-valued
function. -/
theorem smulSum_add_right (a : S → ℤ) (v v' : S → M) :
    smulSum a (v + v') = smulSum a v + smulSum a v' := by
  simp [smulSum, smul_add, Finset.sum_add_distrib]

/-- **Additive pairing of a scalar multiple.** The additive pairing commutes with scalar
multiplication. -/
theorem smulSum_smul_right (a : S → ℤ) (r : R) (v : S → M) :
    smulSum a (r • v) = r • smulSum a v := by
  simp only [smulSum_def, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun s _ => smul_comm _ _ _

/-- **Additive pairing at a constant value.** The additive pairing at a constant value is a degree
multiple. -/
theorem smulSum_const (a : S → ℤ) (m : M) :
    smulSum a (fun _ => m) = degreeOn S a • m := by
  simp [smulSum, degreeOn_apply, Finset.sum_smul]

/-- **Additive pairing of a character at a constant value.** On the character lattice, the additive
pairing at a constant value vanishes. -/
theorem smulSum_const_of_mem {a : S → ℤ} (ha : a ∈ characterLattice S)
    (m : M) : smulSum a (fun _ => m) = 0 := by
  rw [smulSum_const, show degreeOn S a = 0 from ha, zero_smul]

end AdditivePairing

section Functoriality

variable {S' : Type*} [Fintype S']

/-- **Degree scaling.** The linear map `f` scales all degrees by the factor `d`:
`degreeOn S' (f a) = d * degreeOn S a` for every `a`. -/
def IsDegreeScaling (f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)) (d : ℤ) : Prop :=
  ∀ a, degreeOn S' (f a) = d * degreeOn S a

/-- **Degree-scaling maps preserve character lattices.** A degree-scaling map sends the character
lattice of `S` into that of `S'`. -/
theorem IsDegreeScaling.map_mem {f : (S → ℤ) →ₗ[ℤ] (S' → ℤ)} {d : ℤ}
    (hf : IsDegreeScaling f d) {a : S → ℤ} (ha : a ∈ characterLattice S) :
    f a ∈ characterLattice S' := by
  rw [characterLattice, LinearMap.mem_ker, hf a,
    show degreeOn S a = 0 from ha, mul_zero]

/-- **Restriction to the character lattices.** The restriction to the character lattices of a linear
map that scales all degrees by a factor `d` (`hf`). -/
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
/-- **Pullback along an equivalence.** Pullback of integer-valued functions along an equivalence. -/
def permMapFun (σ : S ≃ S') : (S → ℤ) →ₗ[ℤ] (S' → ℤ) :=
  LinearMap.funLeft ℤ ℤ σ.symm

omit [Fintype S] [Fintype S'] in
@[simp]
theorem permMapFun_apply (σ : S ≃ S') (a : S → ℤ) (s' : S') :
    permMapFun σ a s' = a (σ.symm s') :=
  rfl

/-- **Pullback preserves degrees.** Pullback along an equivalence preserves degrees. -/
theorem isDegreeScaling_permMapFun (σ : S ≃ S') :
    IsDegreeScaling (permMapFun σ) 1 := by
  intro a
  simp only [degreeOn_apply, permMapFun_apply, one_mul]
  exact Fintype.sum_equiv σ.symm _ _ fun _ => rfl

/-- **Character-lattice map of an equivalence.** The map on character lattices induced by an
equivalence. -/
def permMap (σ : S ≃ S') :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (permMapFun σ) 1 (isDegreeScaling_permMapFun σ)

@[simp]
theorem coe_permMap_apply (σ : S ≃ S') (a : characterLattice S) (s' : S') :
    (permMap σ a : S' → ℤ) s' = (a : S → ℤ) (σ.symm s') :=
  rfl

omit [Fintype S'] in
/-- **Correspondence map on functions.** The linear map `a ↦ (s' ↦ ∑ s, a s * B s s')` on
integer-valued functions given by a correspondence matrix `B`. It is defined for every `B`, and maps
the character lattice of `S` into that of `S'` when all rows of `B` have the same sum
(`corrMap`). -/
def corrMapFun (B : S → S' → ℤ) : (S → ℤ) →ₗ[ℤ] (S' → ℤ) where
  toFun a s' := ∑ s, a s * B s s'
  map_add' a b := by ext s'; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext s'; simp [Finset.mul_sum, mul_assoc]

omit [Fintype S'] in
@[simp]
theorem corrMapFun_apply (B : S → S' → ℤ) (a : S → ℤ) (s' : S') :
    corrMapFun B a s' = ∑ s, a s * B s s' :=
  rfl

/-- **Correspondences with a common row sum scale degrees.** A correspondence whose rows all sum to
`d` scales degrees by `d`. -/
theorem isDegreeScaling_corrMapFun (B : S → S' → ℤ) (d : ℤ)
    (hB : ∀ s, ∑ s', B s s' = d) : IsDegreeScaling (corrMapFun B) d := by
  intro a
  simp only [degreeOn_apply, corrMapFun_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, hB s, mul_comm]

/-- **Character-lattice map of a correspondence with a common row sum.** For a correspondence matrix
`B` whose rows all sum to the same integer `d` (`hB`), the map `corrMapFun B` scales degrees by `d`,
so it restricts to the character lattices. Without a common row sum it need not preserve them:
`B = diag(1, 0)` sends `(1, -1)` to `(1, 0)`, of degree `1`. -/
def corrMap (B : S → S' → ℤ) (d : ℤ) (hB : ∀ s, ∑ s', B s s' = d) :
    characterLattice S →ₗ[ℤ] characterLattice S' :=
  restrictDegZero (corrMapFun B) d (isDegreeScaling_corrMapFun B d hB)

@[simp]
theorem coe_corrMap_apply (B : S → S' → ℤ) (d : ℤ)
    (hB : ∀ s, ∑ s', B s s' = d) (a : characterLattice S) (s' : S') :
    (corrMap B d hB a : S' → ℤ) s' = ∑ s, (a : S → ℤ) s * B s s' :=
  rfl

/-- **Monomials and pullback.** Monomials are compatible with pullback along an equivalence. -/
theorem zpowProd_permMapFun {G : Type*} [CommGroup G] (σ : S ≃ S')
    (a : S → ℤ) (w : S' → G) :
    zpowProd (permMapFun σ a) w = zpowProd a (w ∘ σ) := by
  simp only [zpowProd, permMapFun_apply, Function.comp_apply]
  exact Fintype.prod_equiv σ.symm _ _ fun _ => by simp

/-- **Monomials and correspondences.** Monomials are compatible with the correspondence map
`corrMapFun B`, for every correspondence matrix `B`. -/
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

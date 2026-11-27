/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.Kernels
public import MathlibExt.Algebra.Algebra.NonUnitalIdeal.KSplit
public import MathlibExt.Algebra.NonUnitalSubalgebra.Quotient
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Fintype.BigOperators

/-!
# Split tensor words and their complete colour coordinates

Let q : A → A/I have a ground-linear section s, and let p(a) = a − s(q(a)) be the associated
projection to I. A Boolean colour chooses I at a false position and A/I at a true position.
The tensor product of these position modules is a coloured word W_c.

The maps J_c : W_c → A^⊗N use ideal inclusion or s in each position; the reverse maps P_c use
p or q. They satisfy P_c J_c = id, P_d J_c = 0 for distinct colours and ∑ c J_c P_c = id. Thus
the finite family of coloured tensor coordinates is linearly equivalent to the ambient tensor
power, with forward map given by summation and inverse by all P_c.

Tensoring these split identities with an arbitrary k-module V gives the same coordinate and
reconstruction formulas while keeping V fixed. The splitting is k-linear and imposes no
multiplicative equation on its section.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators NonUnitalSubalgebra.Quotient

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]

/-- Let k be commutative, A a nonunital k-module ring and I a nonunital k-subalgebra.
splitWordEntry false is the module I, and splitWordEntry true is the module A/I, both in A's
carrier universe. -/
def splitWordEntry (colour : Bool) : ModuleCat.{v} k :=
  if colour then ModuleCat.of k I.Quotient else ModuleCat.of k I.Algebra

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For c : Bool, splitWordEntryMap c : E_c →ₗ[k] A is the ideal
inclusion when c is false and s.sectionMap when c is true. -/
def splitWordEntryMap (splitting : I.KSplit) (colour : Bool) :
    splitWordEntry k A I colour →ₗ[k] A := by
  cases colour with
  | false => exact (I.subtypeHom : I.Algebra →ₗ[k] A)
  | true => exact splitting.sectionMap

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For c : Bool, splitWordEntryProjection c : A →ₗ[k] E_c is p when c is
false and q when c is true. -/
def splitWordEntryProjection (splitting : I.KSplit) (colour : Bool) :
    A →ₗ[k] splitWordEntry k A I colour := by
  cases colour with
  | false => exact splitting.projection
  | true => exact NonUnitalSubalgebra.Quotient.mkL I

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For c : Bool and a : E_c, applying splitWordEntryProjection c after
splitWordEntryMap c returns a. The false case is p ∘ inclusion = id_I and the true case is q ∘
s = id_(A/I). -/
theorem splitWordEntryProjection_leftInverse (splitting : I.KSplit) (colour : Bool)
    (a : splitWordEntry k A I colour) :
    splitWordEntryProjection k A I splitting colour
        (splitWordEntryMap k A I splitting colour a) = a := by
  cases colour with
  | false => exact splitting.projection_subtype a
  | true => exact splitting.quotient_section a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For different source and target colours c,d : Bool,
splitWordEntryProjection d ∘ splitWordEntryMap c = 0. The two cases use q ∘ inclusion = 0 and
p ∘ s = 0. -/
theorem splitWordEntryProjection_map_zero (splitting : I.KSplit)
    (source target : Bool) (h : source ≠ target)
    (a : splitWordEntry k A I source) :
    splitWordEntryProjection k A I splitting target
        (splitWordEntryMap k A I splitting source a) = 0 := by
  cases source <;> cases target
  · exact False.elim (h rfl)
  · change NonUnitalSubalgebra.Quotient.mkL I a.val = 0
    exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr a.property
  · exact splitting.projection_section a
  · exact False.elim (h rfl)

variable {N : ℕ}

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For i : Fin N, splitWordPosition c i is E_(c i), retaining the
position i and its chosen ideal or quotient module. -/
def splitWordPosition (colour : Fin N → Bool) (i : Fin N) : ModuleCat.{v} k :=
  splitWordEntry k A I (colour i)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For i : Fin N, splitWordPositionMap c i : E_(c i) →ₗ[k] A is ideal
inclusion for c i = false and s.sectionMap for c i = true. -/
def splitWordPositionMap (splitting : I.KSplit) (colour : Fin N → Bool) (i : Fin N) :
    splitWordPosition k A I colour i →ₗ[k] A :=
  splitWordEntryMap k A I splitting (colour i)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For i : Fin N, splitWordPositionProjection c i : A →ₗ[k] E_(c i) is
p for c i = false and q for c i = true. -/
def splitWordPositionProjection (splitting : I.KSplit) (colour : Fin N → Bool)
    (i : Fin N) : A →ₗ[k] splitWordPosition k A I colour i :=
  splitWordEntryProjection k A I splitting (colour i)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For i : Fin N and a : E_(c i), the position projection after the
position map equals a. -/
theorem splitWordPositionProjection_leftInverse (splitting : I.KSplit)
    (colour : Fin N → Bool) (i : Fin N) (a : splitWordPosition k A I colour i) :
    splitWordPositionProjection k A I splitting colour i
        (splitWordPositionMap k A I splitting colour i a) = a :=
  splitWordEntryProjection_leftInverse k A I splitting (colour i) a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. Let c,d : Fin N → Bool and i : Fin N satisfy c i ≠ d i. The
d-position projection of the c-position map is zero on E_(c i). -/
theorem splitWordPositionProjection_map_zero (splitting : I.KSplit)
    (source target : Fin N → Bool) (i : Fin N) (h : source i ≠ target i)
    (a : splitWordPosition k A I source i) :
    splitWordPositionProjection k A I splitting target i
        (splitWordPositionMap k A I splitting source i a) = 0 :=
  splitWordEntryProjection_map_zero k A I splitting (source i) (target i) h a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For i : Fin N with c i = true and a ∈ I.toSubmodule,
splitWordPositionProjection c i a = 0, since this coordinate is q. -/
theorem splitWordPositionProjection_ideal_zero (splitting : I.KSplit)
    (colour : Fin N → Bool) (i : Fin N) (hi : colour i = true)
    (a : A) (ha : a ∈ I.toSubmodule) :
    splitWordPositionProjection k A I splitting colour i a = 0 := by
  change splitWordEntryProjection k A I splitting (colour i) a = 0
  rw [hi]
  change NonUnitalSubalgebra.Quotient.mkL I a = 0
  exact (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr ha

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). splitWordTensor c is PiTensorProduct k (fun i => E_(c i)), a tensor
of length N with its positions unchanged. -/
abbrev splitWordTensor (colour : Fin N → Bool) : Type (max u v) :=
  PiTensorProduct k (fun i : Fin N => splitWordPosition k A I colour i)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). splitWordToAmbient c : W_c →ₗ[k] A^⊗N is the tensor map of
splitWordPositionMap in each position; its ideal factors are included and quotient factors are
lifted by s. -/
def splitWordToAmbient (splitting : I.KSplit) (colour : Fin N → Bool) :
    splitWordTensor k A I colour →ₗ[k] TensorPower k N A :=
  PiTensorProduct.map (splitWordPositionMap k A I splitting colour)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). splitAmbientToWord c : A^⊗N →ₗ[k] W_c tensors p or q at each
position according to c. -/
def splitAmbientToWord (splitting : I.KSplit) (colour : Fin N → Bool) :
    TensorPower k N A →ₗ[k] splitWordTensor k A I colour :=
  PiTensorProduct.map (splitWordPositionProjection k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For a_i : E_(c i), splitWordToAmbient c (tprod a) = tprod(i ↦
splitWordPositionMap c i (a_i)). -/
theorem splitWordToAmbient_tprod (splitting : I.KSplit) (colour : Fin N → Bool)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i) :
    splitWordToAmbient k A I splitting colour (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k
        (fun i => splitWordPositionMap k A I splitting colour i (a i)) :=
  PiTensorProduct.map_tprod _ _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). For a : Fin N → A, splitAmbientToWord c (tprod a) = tprod(i ↦
splitWordPositionProjection c i a_i). -/
theorem splitAmbientToWord_tprod (splitting : I.KSplit) (colour : Fin N → Bool)
    (a : Fin N → A) :
    splitAmbientToWord k A I splitting colour (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k
        (fun i => splitWordPositionProjection k A I splitting colour i (a i)) :=
  PiTensorProduct.map_tprod _ _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For every colour c, P_c
∘ J_c = id_(W_c). Tensoring the position retraction identities gives this whole-word
retraction. -/
theorem splitAmbientToWord_comp_splitWordToAmbient (splitting : I.KSplit)
    (colour : Fin N → Bool) :
    (splitAmbientToWord k A I splitting colour).comp
        (splitWordToAmbient k A I splitting colour) = LinearMap.id := by
  have hi (i : Fin N) :
      (splitWordPositionProjection k A I splitting colour i).comp
          (splitWordPositionMap k A I splitting colour i) = LinearMap.id := by
    apply LinearMap.ext
    intro a
    exact splitWordPositionProjection_leftInverse k A I splitting colour i a
  rw [splitAmbientToWord, splitWordToAmbient, ← PiTensorProduct.map_comp]
  simp_rw [hi]
  exact PiTensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For colours c,d : Fin N → Bool with c ≠ d, let J_c and P_d be their
factorwise word map and projection. Then P_d ∘ J_c = 0. -/
theorem splitAmbientToWord_comp_splitWordToAmbient_zero (splitting : I.KSplit)
    (source target : Fin N → Bool) (h : source ≠ target) :
    (splitAmbientToWord k A I splitting target).comp
        (splitWordToAmbient k A I splitting source) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin N, source i ≠ target i := by
    by_contra hn
    apply h
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  change splitAmbientToWord k A I splitting target
      (splitWordToAmbient k A I splitting source (PiTensorProduct.tprod k a)) = 0
  rw [splitWordToAmbient_tprod, splitAmbientToWord_tprod]
  exact (PiTensorProduct.tprod k).map_coord_zero i
    (splitWordPositionProjection_map_zero k A I splitting source target i hi (a i))

private def splitWordEntryEnd (splitting : I.KSplit) (colour : Bool) : A →ₗ[k] A :=
  (splitWordEntryMap k A I splitting colour).comp
    (splitWordEntryProjection k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
private theorem splitWordEntryEnd_sum (splitting : I.KSplit) :
    (∑ colour : Bool, splitWordEntryEnd k A I splitting colour) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  rw [Fintype.sum_bool, LinearMap.add_apply]
  change splitting.sectionMap (NonUnitalSubalgebra.Quotient.mkL I a) +
    (splitting.projection a : A) = a
  rw [add_comm]
  exact splitting.reconstruct a

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For N : ℕ and the factorwise maps J_c,P_c, ∑ c : Fin N → Bool, J_c ∘
P_c = id_(A^⊗N). This is a finite sum over all Boolean words. -/
theorem splitWordToAmbient_sum_comp_splitAmbientToWord (splitting : I.KSplit) (N : ℕ) :
    (∑ colour : Fin N → Bool,
      (splitWordToAmbient k A I splitting colour).comp
        (splitAmbientToWord k A I splitting colour)) = LinearMap.id := by
  classical
  have hexpand :
      PiTensorProduct.map
          (fun _ : Fin N => ∑ b : Bool, splitWordEntryEnd k A I splitting b) =
        ∑ colour : Fin N → Bool,
          PiTensorProduct.map (fun i => splitWordEntryEnd k A I splitting (colour i)) :=
    (PiTensorProduct.mapMultilinear k (fun _ : Fin N => A) (fun _ : Fin N => A)).map_sum
      (fun (_ : Fin N) (b : Bool) => splitWordEntryEnd k A I splitting b)
  rw [splitWordEntryEnd_sum, PiTensorProduct.map_id] at hexpand
  calc
    (∑ colour : Fin N → Bool,
        (splitWordToAmbient k A I splitting colour).comp
          (splitAmbientToWord k A I splitting colour)) =
        ∑ colour : Fin N → Bool,
          PiTensorProduct.map (fun i => splitWordEntryEnd k A I splitting (colour i)) := by
      apply Finset.sum_congr rfl
      intro colour _
      rw [splitWordToAmbient, splitAmbientToWord, ← PiTensorProduct.map_comp]
      rfl
    _ = LinearMap.id := hexpand.symm

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For x : A^⊗N, the factorwise maps satisfy ∑ c : Fin N → Bool,
J_c(P_c(x)) = x. -/
theorem splitWord_reconstruct (splitting : I.KSplit) (x : TensorPower k N A) :
    (∑ colour : Fin N → Bool,
      splitWordToAmbient k A I splitting colour
        (splitAmbientToWord k A I splitting colour x)) = x := by
  have h := congrArg (fun f : TensorPower k N A →ₗ[k] TensorPower k N A => f x)
    (splitWordToAmbient_sum_comp_splitAmbientToWord k A I splitting N)
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using h

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). splitWordCoordinates N is the module Π c : Fin N → Bool, W_c. The
colour type is finite, and all N-position words are included. -/
abbrev splitWordCoordinates (N : ℕ) : Type (max u v) :=
  ∀ colour : Fin N → Bool, splitWordTensor k A I colour

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q.
ambientToSplitWordCoordinates maps x : A^⊗N to the family c ↦ P_c(x) in splitWordCoordinates
N. -/
def ambientToSplitWordCoordinates (splitting : I.KSplit) (N : ℕ) :
    TensorPower k N A →ₗ[k] splitWordCoordinates k A I N :=
  LinearMap.pi (fun colour => splitAmbientToWord k A I splitting colour)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q.
splitWordCoordinatesToAmbient sends a family x = (x_c) to ∑ c, J_c(x_c) in A^⊗N. -/
def splitWordCoordinatesToAmbient (splitting : I.KSplit) (N : ℕ) :
    splitWordCoordinates k A I N →ₗ[k] TensorPower k N A :=
  ∑ colour : Fin N → Bool,
    (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. The reconstruction map
ΣJ_c composed after x ↦ (P_c(x)) is id_(A^⊗N). -/
theorem splitWordCoordinatesToAmbient_comp_ambientToSplitWordCoordinates
    (splitting : I.KSplit) (N : ℕ) :
    (splitWordCoordinatesToAmbient k A I splitting N).comp
        (ambientToSplitWordCoordinates k A I splitting N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (∑ colour : Fin N → Bool,
      (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour))
        (ambientToSplitWordCoordinates k A I splitting N x) = x
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    ambientToSplitWordCoordinates, LinearMap.pi_apply] using
      (splitWord_reconstruct k A I splitting x)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. The all-coordinate map
composed after (x_c) ↦ ∑ c J_c(x_c) is the identity on Π c, W_c, by colour orthogonality. -/
theorem ambientToSplitWordCoordinates_comp_splitWordCoordinatesToAmbient
    (splitting : I.KSplit) (N : ℕ) :
    (ambientToSplitWordCoordinates k A I splitting N).comp
        (splitWordCoordinatesToAmbient k A I splitting N) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext target
  change splitAmbientToWord k A I splitting target
      ((∑ source : Fin N → Bool,
        (splitWordToAmbient k A I splitting source).comp (LinearMap.proj source)) x) = x target
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum]
  have hterm (source : Fin N → Bool) :
      splitAmbientToWord k A I splitting target
          (splitWordToAmbient k A I splitting source (x source)) =
        if source = target then x target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (x target))
        (splitAmbientToWord_comp_splitWordToAmbient k A I splitting target)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (x source))
        (splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source target h)
  simp_rw [hterm]
  simp

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q.
splitWordCoordinatesEquiv : (Π c, W_c) ≃ₗ[k] A^⊗N has forward map (x_c) ↦ ∑ c J_c(x_c) and
inverse x ↦ (P_c(x)). -/
def splitWordCoordinatesEquiv (splitting : I.KSplit) (N : ℕ) :
    splitWordCoordinates k A I N ≃ₗ[k] TensorPower k N A :=
  { splitWordCoordinatesToAmbient k A I splitting N with
    invFun := ambientToSplitWordCoordinates k A I splitting N
    left_inv := fun x => congrArg (fun f => f x)
      (ambientToSplitWordCoordinates_comp_splitWordCoordinatesToAmbient k A I splitting N)
    right_inv := fun x => congrArg (fun f => f x)
      (splitWordCoordinatesToAmbient_comp_ambientToSplitWordCoordinates k A I splitting N) }

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For x = (x_c) :
splitWordCoordinates N, splitWordCoordinatesEquiv x = ∑ c, J_c(x_c). -/
theorem splitWordCoordinatesEquiv_apply (splitting : I.KSplit) (N : ℕ)
    (x : splitWordCoordinates k A I N) :
    splitWordCoordinatesEquiv k A I splitting N x =
      ∑ colour : Fin N → Bool, splitWordToAmbient k A I splitting colour (x colour) := by
  change (∑ colour : Fin N → Bool,
    (splitWordToAmbient k A I splitting colour).comp (LinearMap.proj colour)) x = _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. For x : A^⊗N and a
colour c, (splitWordCoordinatesEquiv.symm x) c = P_c(x). -/
theorem splitWordCoordinatesEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : TensorPower k N A) (colour : Fin N → Bool) :
    (splitWordCoordinatesEquiv k A I splitting N).symm x colour =
      splitAmbientToWord k A I splitting colour x := rfl

variable (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. coefficientSplitWordToAmbient c : V
⊗[k] W_c →ₗ[k] V ⊗[k] A^⊗N is J_c^V, applying the coloured inclusion/section maps only to the
word factors. -/
def coefficientSplitWordToAmbient (splitting : I.KSplit) (colour : Fin N → Bool) :
    V ⊗[k] splitWordTensor k A I colour →ₗ[k] V ⊗[k] TensorPower k N A :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (splitWordToAmbient k A I splitting colour)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. coefficientSplitAmbientToWord c : V
⊗[k] A^⊗N →ₗ[k] V ⊗[k] W_c is P_c^V, applying the ideal or quotient projections only to the
word factors. -/
def coefficientSplitAmbientToWord (splitting : I.KSplit) (colour : Fin N → Bool) :
    V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] splitWordTensor k A I colour :=
  TensorProduct.map (LinearMap.id : V →ₗ[k] V)
    (splitAmbientToWord k A I splitting colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For v : V and a_i : E_(c i),
J_c^V(v ⊗ tprod a) = v ⊗ tprod(i ↦ splitWordPositionMap c i (a_i)). -/
theorem coefficientSplitWordToAmbient_tprod (splitting : I.KSplit)
    (colour : Fin N → Bool) (v : V)
    (a : ∀ i : Fin N, splitWordPosition k A I colour i) :
    coefficientSplitWordToAmbient k A I V splitting colour
        (v ⊗ₜ[k] PiTensorProduct.tprod k a) =
      v ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => splitWordPositionMap k A I splitting colour i (a i)) := by
  rw [coefficientSplitWordToAmbient, TensorProduct.map_tmul, LinearMap.id_apply,
    splitWordToAmbient_tprod]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For v : V and a : Fin N → A,
P_c^V(v ⊗ tprod a) = v ⊗ tprod(i ↦ splitWordPositionProjection c i a_i). -/
theorem coefficientSplitAmbientToWord_tprod (splitting : I.KSplit)
    (colour : Fin N → Bool) (v : V) (a : Fin N → A) :
    coefficientSplitAmbientToWord k A I V splitting colour
        (v ⊗ₜ[k] PiTensorProduct.tprod k a) =
      v ⊗ₜ[k] PiTensorProduct.tprod k
        (fun i => splitWordPositionProjection k A I splitting colour i (a i)) := by
  rw [coefficientSplitAmbientToWord, TensorProduct.map_tmul, LinearMap.id_apply,
    splitAmbientToWord_tprod]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For every c, P_c^V ∘ J_c^V = id_(V
⊗[k] W_c), by tensoring the position retractions with id_V. -/
theorem coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient
    (splitting : I.KSplit) (colour : Fin N → Bool) :
    (coefficientSplitAmbientToWord k A I V splitting colour).comp
        (coefficientSplitWordToAmbient k A I V splitting colour) = LinearMap.id := by
  rw [coefficientSplitAmbientToWord, coefficientSplitWordToAmbient,
    ← TensorProduct.map_comp, LinearMap.id_comp, splitAmbientToWord_comp_splitWordToAmbient]
  exact TensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For colours c ≠ d, P_d^V ∘ J_c^V =
0 as a map V ⊗ W_c → V ⊗ W_d. -/
theorem coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
    (splitting : I.KSplit) (source target : Fin N → Bool) (h : source ≠ target) :
    (coefficientSplitAmbientToWord k A I V splitting target).comp
        (coefficientSplitWordToAmbient k A I V splitting source) = 0 := by
  rw [coefficientSplitAmbientToWord, coefficientSplitWordToAmbient,
    ← TensorProduct.map_comp, LinearMap.id_comp,
    splitAmbientToWord_comp_splitWordToAmbient_zero k A I splitting source target h]
  exact TensorProduct.map_zero_right _

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For every N : ℕ, ∑ colour : Fin N →
Bool, J_colour^V ∘ P_colour^V = id_(V ⊗[k] A^⊗N). The identity holds for arbitrary V. -/
theorem coefficientSplitWordToAmbient_sum_comp_coefficientSplitAmbientToWord
    (splitting : I.KSplit) (N : ℕ) :
    (∑ colour : Fin N → Bool,
      (coefficientSplitWordToAmbient k A I V splitting colour).comp
        (coefficientSplitAmbientToWord k A I V splitting colour)) = LinearMap.id := by
  classical
  have hsum :
      TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (∑ colour : Fin N → Bool,
            (splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) =
        ∑ colour : Fin N → Bool,
          TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            ((splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) :=
    map_sum (LinearMap.lTensorHom V) _ _
  calc
    (∑ colour : Fin N → Bool,
        (coefficientSplitWordToAmbient k A I V splitting colour).comp
          (coefficientSplitAmbientToWord k A I V splitting colour)) =
        ∑ colour : Fin N → Bool,
          TensorProduct.map (LinearMap.id : V →ₗ[k] V)
            ((splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) := by
      apply Finset.sum_congr rfl
      intro colour _
      rw [coefficientSplitWordToAmbient, coefficientSplitAmbientToWord,
        ← TensorProduct.map_comp, LinearMap.id_comp]
    _ = TensorProduct.map (LinearMap.id : V →ₗ[k] V)
          (∑ colour : Fin N → Bool,
            (splitWordToAmbient k A I splitting colour).comp
              (splitAmbientToWord k A I splitting colour)) := hsum.symm
    _ = LinearMap.id := by
      rw [splitWordToAmbient_sum_comp_splitAmbientToWord]
      exact TensorProduct.map_id

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For x : V ⊗[k] A^⊗N, ∑ colour,
J_colour^V(P_colour^V(x)) = x. -/
theorem coefficientSplitWord_reconstruct (splitting : I.KSplit)
    (x : V ⊗[k] TensorPower k N A) :
    (∑ colour : Fin N → Bool,
      coefficientSplitWordToAmbient k A I V splitting colour
        (coefficientSplitAmbientToWord k A I V splitting colour x)) = x := by
  have h := congrArg
    (fun f : V ⊗[k] TensorPower k N A →ₗ[k] V ⊗[k] TensorPower k N A => f x)
    (coefficientSplitWordToAmbient_sum_comp_coefficientSplitAmbientToWord k A I V splitting N)
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using h

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. coefficientSplitWordCoordinates N
is Π colour : Fin N → Bool, V ⊗[k] W_colour. For k : Type u, A : Type v and V : Type w, its
carrier universe is max u v w. -/
abbrev coefficientSplitWordCoordinates (N : ℕ) : Type (max u v w) :=
  ∀ colour : Fin N → Bool, V ⊗[k] splitWordTensor k A I colour

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c.
coefficientAmbientToSplitWordCoordinates maps x : V ⊗ A^⊗N to the family colour ↦
P_colour^V(x). -/
def coefficientAmbientToSplitWordCoordinates (splitting : I.KSplit) (N : ℕ) :
    V ⊗[k] TensorPower k N A →ₗ[k] coefficientSplitWordCoordinates k A I V N :=
  LinearMap.pi (fun colour => coefficientSplitAmbientToWord k A I V splitting colour)

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c.
coefficientSplitWordCoordinatesToAmbient sends a family x = (x_colour) to ∑ colour,
J_colour^V(x_colour) in V ⊗[k] A^⊗N. -/
def coefficientSplitWordCoordinatesToAmbient (splitting : I.KSplit) (N : ℕ) :
    coefficientSplitWordCoordinates k A I V N →ₗ[k] V ⊗[k] TensorPower k N A :=
  ∑ colour : Fin N → Bool,
    (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. The coefficient reconstruction map
composed after the complete projection family is id_(V ⊗[k] A^⊗N). -/
theorem coefficientSplitWordCoordinatesToAmbient_comp_coefficientAmbientToSplitWordCoordinates
    (splitting : I.KSplit) (N : ℕ) :
    (coefficientSplitWordCoordinatesToAmbient k A I V splitting N).comp
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change (∑ colour : Fin N → Bool,
      (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour))
        (coefficientAmbientToSplitWordCoordinates k A I V splitting N x) = x
  simpa only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    coefficientAmbientToSplitWordCoordinates, LinearMap.pi_apply] using
      (coefficientSplitWord_reconstruct k A I V splitting x)

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. The complete coefficient projection
family composed after reconstruction is the identity on Π colour, V ⊗[k] W_colour. -/
theorem coefficientAmbientToSplitWordCoordinates_comp_coefficientSplitWordCoordinatesToAmbient
    (splitting : I.KSplit) (N : ℕ) :
    (coefficientAmbientToSplitWordCoordinates k A I V splitting N).comp
        (coefficientSplitWordCoordinatesToAmbient k A I V splitting N) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  funext target
  change coefficientSplitAmbientToWord k A I V splitting target
      ((∑ source : Fin N → Bool,
        (coefficientSplitWordToAmbient k A I V splitting source).comp (LinearMap.proj source)) x) =
      x target
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [map_sum]
  have hterm (source : Fin N → Bool) :
      coefficientSplitAmbientToWord k A I V splitting target
          (coefficientSplitWordToAmbient k A I V splitting source (x source)) =
        if source = target then x target else 0 := by
    by_cases h : source = target
    · subst source
      rw [ite_eq_left rfl]
      exact congrArg (fun f => f (x target))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient k A I V splitting target)
    · rw [ite_eq_right h]
      exact congrArg (fun f => f (x source))
        (coefficientSplitAmbientToWord_comp_coefficientSplitWordToAmbient_zero
          k A I V splitting source target h)
  simp_rw [hterm]
  simp

/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c.
coefficientSplitWordCoordinatesEquiv is the k-linear equivalence (Π colour, V ⊗[k] W_colour)
≃ₗ[k] V ⊗[k] A^⊗N. Its forward map sums J_colour^V and its inverse collects P_colour^V. -/
def coefficientSplitWordCoordinatesEquiv (splitting : I.KSplit) (N : ℕ) :
    coefficientSplitWordCoordinates k A I V N ≃ₗ[k] V ⊗[k] TensorPower k N A :=
  { coefficientSplitWordCoordinatesToAmbient k A I V splitting N with
    invFun := coefficientAmbientToSplitWordCoordinates k A I V splitting N
    left_inv := fun x => congrArg (fun f => f x)
      (coefficientAmbientToSplitWordCoordinates_comp_coefficientSplitWordCoordinatesToAmbient
        k A I V splitting N)
    right_inv := fun x => congrArg (fun f => f x)
      (coefficientSplitWordCoordinatesToAmbient_comp_coefficientAmbientToSplitWordCoordinates
        k A I V splitting N) }

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For a family x = (x_colour),
coefficientSplitWordCoordinatesEquiv x = ∑ colour, J_colour^V(x_colour). -/
theorem coefficientSplitWordCoordinatesEquiv_apply (splitting : I.KSplit) (N : ℕ)
    (x : coefficientSplitWordCoordinates k A I V N) :
    coefficientSplitWordCoordinatesEquiv k A I V splitting N x =
      ∑ colour : Fin N → Bool,
        coefficientSplitWordToAmbient k A I V splitting colour (x colour) := by
  change (∑ colour : Fin N → Bool,
    (coefficientSplitWordToAmbient k A I V splitting colour).comp (LinearMap.proj colour)) x = _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

omit [IsScalarTower k A A] [SMulCommClass k A A] [I.IsTwoSided] in
/-- Let k be a commutative ring, A a nonunital ring with a k-module structure and I a nonunital
k-subalgebra. Let q : A → A/I and s : I.KSplit be a k-linear section with q ∘ s = id; write
p(a) = a − s(q(a)) in I. For a colour c : Fin N → Bool, put E_false = I, E_true = A/I and W_c
= ⊗[k] i : Fin N, E_(c i). Let J_c : W_c → A^⊗N tensor the inclusions I → A and sections s,
and let P_c : A^⊗N → W_c tensor the projections p and quotient maps q. Let V be an arbitrary
k-module. Write J_c^V = id_V ⊗ J_c and P_c^V = id_V ⊗ P_c. For x : V ⊗[k] A^⊗N and a colour,
coefficientSplitWordCoordinatesEquiv.symm x colour = P_colour^V(x). -/
theorem coefficientSplitWordCoordinatesEquiv_symm_apply (splitting : I.KSplit) (N : ℕ)
    (x : V ⊗[k] TensorPower k N A) (colour : Fin N → Bool) :
    (coefficientSplitWordCoordinatesEquiv k A I V splitting N).symm x colour =
      coefficientSplitAmbientToWord k A I V splitting colour x := rfl

end ModuleCat.Algebra.Hochschild.NonUnital

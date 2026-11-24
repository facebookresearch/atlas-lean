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

public import MathlibExt.GroupTheory.PermutationBilinearMonomialExtension
public import MathlibExt.GroupTheory.PermutationBilinearTitsAction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section

namespace PermutationSchurCocycle

open PermutationBilinearCocycle

variable {n : Nat}

/-- Roots are increasing index pairs, ordered lexicographically. -/
def Root (n : Nat) := { x : Fin n × Fin n // x.1 < x.2 }

noncomputable instance rootLinearOrder (n : Nat) :
    LinearOrder (Root n) :=
  LinearOrder.lift' (fun r : Root n => toLex r.1) fun _ _ h =>
    Subtype.ext (toLex.injective h)

instance Root.fintype (n : Nat) : Fintype (Root n) :=
  inferInstanceAs (Fintype { x : Fin n × Fin n // x.1 < x.2 })

/-- The ordered two-index root associated with two distinct finite coordinates. -/
def mkRoot {n : Nat} (a b : Fin n) (h : a ≠ b) : Root n :=
  ⟨(min a b, max a b), min_lt_max.mpr h⟩

@[simp]
theorem mkRoot_of_lt {n : Nat} {a b : Fin n} (h : a < b) :
    mkRoot a b h.ne = ⟨(a, b), h⟩ := by
  apply Subtype.ext
  simp [mkRoot, min_eq_left h.le, max_eq_right h.le]

@[simp]
theorem mkRoot_of_gt {n : Nat} {a b : Fin n} (h : b < a) :
    mkRoot a b h.ne' = ⟨(b, a), h⟩ := by
  apply Subtype.ext
  simp [mkRoot, min_eq_right h.le, max_eq_left h.le]

/-- The permutation induced on the ordered two-index roots. -/
def rootPerm {n : Nat} (p : Equiv.Perm (Fin n)) :
    Equiv.Perm (Root n) where
  toFun r :=
    mkRoot (p r.1.1) (p r.1.2) (p.injective.ne r.2.ne)
  invFun r :=
    mkRoot (p⁻¹ r.1.1) (p⁻¹ r.1.2) (p⁻¹.injective.ne r.2.ne)
  left_inv r := by
    apply Subtype.ext
    have ha : p⁻¹ (p r.1.1) = r.1.1 := p.symm_apply_apply _
    have hb : p⁻¹ (p r.1.2) = r.1.2 := p.symm_apply_apply _
    by_cases hp : p r.1.1 < p r.1.2
    · simp only [mkRoot, min_eq_left hp.le, max_eq_right hp.le,
        ha, hb, min_eq_left r.2.le, max_eq_right r.2.le]
    · have hp' : p r.1.2 < p r.1.1 :=
        lt_of_le_of_ne (le_of_not_gt hp)
          (p.injective.ne r.2.ne).symm
      simp only [mkRoot, min_eq_right hp'.le, max_eq_left hp'.le,
        ha, hb, min_eq_right r.2.le, max_eq_left r.2.le]
  right_inv r := by
    apply Subtype.ext
    have ha : p (p⁻¹ r.1.1) = r.1.1 := p.apply_symm_apply _
    have hb : p (p⁻¹ r.1.2) = r.1.2 := p.apply_symm_apply _
    by_cases hp : p⁻¹ r.1.1 < p⁻¹ r.1.2
    · simp only [mkRoot, min_eq_left hp.le, max_eq_right hp.le,
        ha, hb, min_eq_left r.2.le, max_eq_right r.2.le]
    · have hp' : p⁻¹ r.1.2 < p⁻¹ r.1.1 :=
        lt_of_le_of_ne (le_of_not_gt hp)
          (p⁻¹.injective.ne r.2.ne).symm
      simp only [mkRoot, min_eq_right hp'.le, max_eq_left hp'.le,
        ha, hb, min_eq_right r.2.le, max_eq_left r.2.le]

@[simp]
theorem rootPerm_apply {n : Nat} (p : Equiv.Perm (Fin n))
    (r : Root n) :
    rootPerm p r =
      mkRoot (p r.1.1) (p r.1.2) (p.injective.ne r.2.ne) :=
  rfl

theorem rootPerm_one {n : Nat} :
    rootPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Equiv.Perm.ext
  intro r
  apply Subtype.ext
  simp only [rootPerm_apply]
  simp [mkRoot, min_eq_left r.2.le, max_eq_right r.2.le]

theorem rootPerm_mul {n : Nat} (p q : Equiv.Perm (Fin n)) :
    rootPerm (p * q) = rootPerm p * rootPerm q := by
  apply Equiv.Perm.ext
  intro r
  apply Subtype.ext
  simp only [rootPerm_apply, Equiv.Perm.mul_apply]
  by_cases hq : q r.1.1 < q r.1.2
  · simp [mkRoot, min_eq_left hq.le, max_eq_right hq.le]
  · have hq' : q r.1.2 < q r.1.1 :=
      lt_of_le_of_ne (le_of_not_gt hq)
        (q.injective.ne r.2.ne).symm
    simp [mkRoot, min_eq_right hq'.le, max_eq_left hq'.le,
      min_comm, max_comm]

/-- The action on ordered roots as a permutation-group homomorphism. -/
def rootPermHom (n : Nat) :
    Equiv.Perm (Fin n) →* Equiv.Perm (Root n) where
  toFun := rootPerm
  map_one' := rootPerm_one
  map_mul' := rootPerm_mul

theorem rootPerm_inv {n : Nat} (p : Equiv.Perm (Fin n)) :
    rootPerm p⁻¹ = (rootPerm p)⁻¹ := by
  exact map_inv (rootPermHom n) p

/-- The sign bit of the specified root under the given permutation. -/
def rootSignBit {n : Nat} (p : Equiv.Perm (Fin n))
    (r : Root n) : ZMod 2 :=
  if p⁻¹ r.1.1 < p⁻¹ r.1.2 then 0 else 1

/-- The root sign under the multiplicative tag on the order-two coefficient group. -/
def rootSign {n : Nat} (p : Equiv.Perm (Fin n)) :
    Root n → Multiplicative (ZMod 2) :=
  fun r => Multiplicative.ofAdd (rootSignBit p r)

@[simp]
theorem rootSign_one {n : Nat} :
    rootSign (1 : Equiv.Perm (Fin n)) = 1 := by
  funext r
  change Multiplicative.ofAdd
      (if ((1 : Equiv.Perm (Fin n))⁻¹ r.1.1) <
        ((1 : Equiv.Perm (Fin n))⁻¹ r.1.2) then 0 else 1) = 1
  simp [r.2]

theorem rootSign_mul {n : Nat} (p q : Equiv.Perm (Fin n)) :
    rootSign (p * q) = rootSign p *
      permute (rootPerm p) (rootSign q) := by
  funext r
  change Multiplicative.ofAdd (rootSignBit (p * q) r) =
    Multiplicative.ofAdd (rootSignBit p r) *
      Multiplicative.ofAdd
        (rootSignBit q ((rootPerm p)⁻¹ r))
  rw [← ofAdd_add]
  congr 1
  rw [← rootPerm_inv]
  let a := p⁻¹ r.1.1
  let b := p⁻¹ r.1.2
  have hab : a ≠ b := p⁻¹.injective.ne r.2.ne
  by_cases hp : a < b
  · have hr : rootPerm p⁻¹ r = mkRoot a b hab := rfl
    rw [hr, mkRoot_of_lt hp]
    have hp0 : p⁻¹ r.1.1 < p⁻¹ r.1.2 := by
      simpa [a, b] using hp
    by_cases hq : q⁻¹ a < q⁻¹ b
    · have hc : (p * q)⁻¹ r.1.1 < (p * q)⁻¹ r.1.2 := by
        change q⁻¹ a < q⁻¹ b
        exact hq
      simp only [rootSignBit, ite_eq_left hc, ite_eq_left hp0,
        ite_eq_left hq, zero_add]
    · have hc : ¬(p * q)⁻¹ r.1.1 < (p * q)⁻¹ r.1.2 := by
        change ¬q⁻¹ a < q⁻¹ b
        exact hq
      simp only [rootSignBit, ite_eq_right hc, ite_eq_left hp0,
        ite_eq_right hq, zero_add]
  · have hp' : b < a :=
      lt_of_le_of_ne (le_of_not_gt hp) hab.symm
    have hr : rootPerm p⁻¹ r = mkRoot a b hab := rfl
    rw [hr, mkRoot_of_gt hp']
    have hp0 : ¬p⁻¹ r.1.1 < p⁻¹ r.1.2 := by
      simpa [a, b] using hp
    by_cases hq : q⁻¹ a < q⁻¹ b
    · have hnot : ¬q⁻¹ b < q⁻¹ a := not_lt_of_ge hq.le
      have hc : (p * q)⁻¹ r.1.1 < (p * q)⁻¹ r.1.2 := by
        change q⁻¹ a < q⁻¹ b
        exact hq
      simp only [rootSignBit, ite_eq_left hc, ite_eq_right hp0,
        ite_eq_right hnot]
      have htwo : (2 : ZMod 2) = 0 :=
        ZMod.natCast_eq_zero_iff_even.mpr ⟨1, rfl⟩
      simpa [one_add_one_eq_two] using htwo.symm
    · have hq' : q⁻¹ b < q⁻¹ a :=
        lt_of_le_of_ne (le_of_not_gt hq)
          (q⁻¹.injective.ne hab).symm
      have hc : ¬(p * q)⁻¹ r.1.1 < (p * q)⁻¹ r.1.2 := by
        change ¬q⁻¹ a < q⁻¹ b
        exact hq
      simp only [rootSignBit, ite_eq_right hc, ite_eq_right hp0,
        ite_eq_left hq', add_zero]

/-- The canonical bicharacter on the multiplicatively tagged order-two coefficients. -/
def bitBicharacter :
    SkewBicharacter (Multiplicative (ZMod 2)) (ZMod 2) where
  toBiadditive :=
    { toFun := fun x =>
        { toFun := fun y => x.toMul.toAdd * y.toMul.toAdd
          map_zero' := by simp
          map_add' := by intro y z; simp [mul_add] }
      map_zero' := by ext y; simp
      map_add' := by intro x y; ext z; simp [add_mul] }
  skew x y := by
    change x.toAdd * y.toAdd = -(y.toAdd * x.toAdd)
    rw [ZMod.neg_eq_self_mod_two, mul_comm]

/-- The signed monomial root representation of the finite permutation group. -/
def rootMonomial (n : Nat) :
    Equiv.Perm (Fin n) →*
      MonomialBase (Multiplicative (ZMod 2)) (Root n) where
  toFun p := ⟨rootSign p, rootPerm p⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact rootSign_one
    · exact rootPerm_one
  map_mul' p q := by
    apply SemidirectProduct.ext
    · exact rootSign_mul p q
    · exact rootPerm_mul p q

section MonomialCocycle

variable {A B ι : Type*} [Group A] [AddCommGroup B]
variable [Fintype ι] [LinearOrder ι]

/-- The specified section of the monomial projection in the bilinear extension. -/
def monomialSection (b : SkewBicharacter A B)
    (x : MonomialBase A ι) : MonomialLift b ι :=
  ⟨⟨x.left, 1⟩, x.right⟩

/-- The additive cocycle computed from the specified monomial section. -/
def monomialAddCocycle (b : SkewBicharacter A B)
    (x y : MonomialBase A ι) : B :=
  lowerSum b x.left (permute x.right y.left) +
    inversionSum b x.right y.left

@[simp]
theorem monomialAddCocycle_eq (b : SkewBicharacter A B)
    (x y : MonomialBase A ι) :
    monomialAddCocycle b x y =
      lowerSum b x.left (permute x.right y.left) +
        inversionSum b x.right y.left :=
  rfl

theorem monomialAddCocycle_cocycle (b : SkewBicharacter A B)
    (x y z : MonomialBase A ι) :
    monomialAddCocycle b x y +
        monomialAddCocycle b (x * y) z =
      monomialAddCocycle b y z +
        monomialAddCocycle b x (y * z) := by
  simp only [monomialAddCocycle_eq, SemidirectProduct.mul_left,
    SemidirectProduct.mul_right, tupleActionHom_apply]
  rw [lowerSum_mul_left, permute_mul, inversionSum_comp,
    permute_mul_tuple, lowerSum_mul_right]
  have htransport := lowerSum_inversion_transport b x.right
    y.left (permute y.right z.left)
  let extra := lowerSum b x.left (permute x.right y.left) +
    lowerSum b x.left (permute x.right (permute y.right z.left)) +
      inversionSum b y.right z.left
  have h := congrArg (fun t : B => t + extra) htransport.symm
  dsimp [extra] at h
  abel_nf at h ⊢
  exact h

end MonomialCocycle

/-- The initial order-two root cocycle computed from the permutation data. -/
noncomputable def rootCocycle0 {n : Nat}
    (p q : Equiv.Perm (Fin n)) : ZMod 2 :=
  monomialAddCocycle bitBicharacter
    (rootMonomial n p) (rootMonomial n q)

theorem rootCocycle0_cocycle {n : Nat}
    (p q r : Equiv.Perm (Fin n)) :
    rootCocycle0 p q + rootCocycle0 (p * q) r =
      rootCocycle0 q r + rootCocycle0 p (q * r) := by
  simpa [rootCocycle0] using
    monomialAddCocycle_cocycle bitBicharacter
      (rootMonomial n p) (rootMonomial n q) (rootMonomial n r)

/-- The order-two parity bit of the specified permutation. -/
def parityBit {n : Nat} (p : Equiv.Perm (Fin n)) : ZMod 2 :=
  (PermutationBilinearTitsAction.parityUnit
    (Multiplicative.ofAdd (1 : ZMod 2)) p).toAdd

theorem parityBit_mul {n : Nat} (p q : Equiv.Perm (Fin n)) :
    parityBit (p * q) = parityBit p + parityBit q := by
  have htwo : (2 : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr ⟨1, rfl⟩
  have heps : Multiplicative.ofAdd (1 : ZMod 2) *
      Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    change Multiplicative.ofAdd ((1 : ZMod 2) + 1) =
      Multiplicative.ofAdd 0
    rw [one_add_one_eq_two, htwo]
  exact congrArg Multiplicative.toAdd
    (PermutationBilinearTitsAction.parityUnit_mul heps p q)

/-- The additive Schur cocycle of the finite permutation group. -/
noncomputable def schurCocycle {n : Nat}
    (p q : Equiv.Perm (Fin n)) : ZMod 2 :=
  rootCocycle0 p q + parityBit p * parityBit q

@[simp]
theorem parityBit_one {n : Nat} :
    parityBit (1 : Equiv.Perm (Fin n)) = 0 := by
  simp [parityBit,
    PermutationBilinearTitsAction.parityUnit_one]

@[simp]
theorem rootCocycle0_one_left {n : Nat}
    (q : Equiv.Perm (Fin n)) : rootCocycle0 1 q = 0 := by
  simp [rootCocycle0, monomialAddCocycle, rootMonomial,
    rootPerm_one, lowerSum_one_left,
    PermutationBilinearCocycle.inversionSum_perm_one]

@[simp]
theorem rootCocycle0_one_right {n : Nat}
    (p : Equiv.Perm (Fin n)) : rootCocycle0 p 1 = 0 := by
  simp [rootCocycle0, monomialAddCocycle, rootMonomial,
    lowerSum_one_right,
    PermutationBilinearCocycle.inversionSum_one_tuple]

@[simp]
theorem schurCocycle_one_left {n : Nat}
    (q : Equiv.Perm (Fin n)) : schurCocycle 1 q = 0 := by
  simp [schurCocycle]

@[simp]
theorem schurCocycle_one_right {n : Nat}
    (p : Equiv.Perm (Fin n)) : schurCocycle p 1 = 0 := by
  simp [schurCocycle]

theorem schurCocycle_cocycle {n : Nat}
    (p q r : Equiv.Perm (Fin n)) :
    schurCocycle p q + schurCocycle (p * q) r =
      schurCocycle q r + schurCocycle p (q * r) := by
  rw [schurCocycle, schurCocycle, schurCocycle, schurCocycle,
    parityBit_mul, parityBit_mul]
  have hroot := rootCocycle0_cocycle p q r
  calc
    rootCocycle0 p q + parityBit p * parityBit q +
          (rootCocycle0 (p * q) r +
            (parityBit p + parityBit q) * parityBit r) =
        (rootCocycle0 p q + rootCocycle0 (p * q) r) +
          (parityBit p * parityBit q +
            (parityBit p + parityBit q) * parityBit r) := by
      ring
    _ = (rootCocycle0 q r + rootCocycle0 p (q * r)) +
          (parityBit p * parityBit q +
            (parityBit p + parityBit q) * parityBit r) := by
      rw [hroot]
    _ = rootCocycle0 q r + parityBit q * parityBit r +
          (rootCocycle0 p (q * r) +
            parityBit p * (parityBit q + parityBit r)) := by
      ring

/-- The Schur cocycle with its additive value under the multiplicative tag. -/
noncomputable def schurCocycleMul {n : Nat}
    (p q : Equiv.Perm (Fin n)) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (schurCocycle p q)

/-- The normalized order-two Schur cocycle of the finite permutation group. -/
noncomputable def schurNormalizedCocycle (n : Nat) :
    NormalizedCocycleExtension.NormalizedCocycle
      (Equiv.Perm (Fin n)) (Multiplicative (ZMod 2)) where
  cocycle := schurCocycleMul
  one_left := by
    intro g
    simp [schurCocycleMul, schurCocycle_one_left]
  one_right := by
    intro g
    simp [schurCocycleMul, schurCocycle_one_right]
  cocycle_assoc := by
    intro p q r
    simp only [schurCocycleMul]
    have h := schurCocycle_cocycle p q r
    calc
      Multiplicative.ofAdd (schurCocycle p q) *
          Multiplicative.ofAdd (schurCocycle (p * q) r) =
        Multiplicative.ofAdd
          (schurCocycle p q + schurCocycle (p * q) r) := by
        rw [← ofAdd_add]
      _ = Multiplicative.ofAdd
            (schurCocycle q r + schurCocycle p (q * r)) := by
        rw [h]
      _ = Multiplicative.ofAdd (schurCocycle p (q * r)) *
            Multiplicative.ofAdd (schurCocycle q r) := by
        rw [ofAdd_add, mul_comm]

private theorem zmod2_eq_zero_or_one (a : ZMod 2) :
    a = 0 ∨ a = 1 := by
  have hv : a.val = 0 ∨ a.val = 1 := by
    have hlt : a.val < 2 := a.val_lt
    omega
  rcases hv with hv0 | hv1
  · left
    have hcast : (a.val : ZMod 2) = a :=
      ZMod.natCast_zmod_val a
    rw [hv0] at hcast
    simp at hcast
    exact hcast.symm
  · right
    have hcast : (a.val : ZMod 2) = a :=
      ZMod.natCast_zmod_val a
    rw [hv1] at hcast
    simp at hcast
    exact hcast.symm

/-- The homomorphism sending the order-two generator to the specified two-torsion element. -/
def zmod2ToA {A : Type*} [AddCommGroup A] (z : A)
    (hz : 2 • z = 0) : ZMod 2 →+ A where
  toFun x := if x = 0 then 0 else z
  map_zero' := by
    rw [ite_eq_left rfl]
  map_add' := by
    intro a b
    have ha := zmod2_eq_zero_or_one a
    have hb := zmod2_eq_zero_or_one b
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · have h0 : (0 : ZMod 2) + 0 = 0 := rfl
      calc
        (if (0 : ZMod 2) + 0 = 0 then (0 : A) else z) =
            if (0 : ZMod 2) = 0 then (0 : A) else z := by
          rw [h0]
        _ = (0 : A) := by rw [ite_eq_left rfl]
        _ = (0 : A) + 0 := by rw [add_zero]
        _ = (if (0 : ZMod 2) = 0 then (0 : A) else z) +
              if (0 : ZMod 2) = 0 then (0 : A) else z := by
          rw [ite_eq_left rfl]
    · have h1n : (1 : ZMod 2) ≠ 0 := by decide
      have h01 : (0 : ZMod 2) + 1 = 1 := rfl
      calc
        (if (0 : ZMod 2) + 1 = 0 then (0 : A) else z) =
            if (1 : ZMod 2) = 0 then (0 : A) else z := by
          rw [h01]
        _ = z := by rw [ite_eq_right h1n]
        _ = (0 : A) + z := by rw [zero_add]
        _ = (if (0 : ZMod 2) = 0 then (0 : A) else z) +
              if (1 : ZMod 2) = 0 then (0 : A) else z := by
          rw [ite_eq_left rfl, ite_eq_right h1n]
    · have h1n : (1 : ZMod 2) ≠ 0 := by decide
      have h10 : (1 : ZMod 2) + 0 = 1 := rfl
      calc
        (if (1 : ZMod 2) + 0 = 0 then (0 : A) else z) =
            if (1 : ZMod 2) = 0 then (0 : A) else z := by
          rw [h10]
        _ = z := by rw [ite_eq_right h1n]
        _ = z + 0 := by rw [add_zero]
        _ = (if (1 : ZMod 2) = 0 then (0 : A) else z) +
              if (0 : ZMod 2) = 0 then (0 : A) else z := by
          rw [ite_eq_right h1n, ite_eq_left rfl]
    · have h1n : (1 : ZMod 2) ≠ 0 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      have hzAdd : z + z = 0 := by
        have h2 : 2 • z = z + z := by rw [two_nsmul]
        rw [← h2]
        exact hz
      calc
        (if (1 : ZMod 2) + 1 = 0 then (0 : A) else z) =
            if (0 : ZMod 2) = 0 then (0 : A) else z := by
          rw [h11]
        _ = (0 : A) := by rw [ite_eq_left rfl]
        _ = z + z := hzAdd.symm
        _ = (if (1 : ZMod 2) = 0 then (0 : A) else z) +
              if (1 : ZMod 2) = 0 then (0 : A) else z := by
          rw [ite_eq_right h1n]

/-- The Schur cocycle mapped to the specified two-torsion coefficient. -/
noncomputable def schurCocycleWith {A : Type*} [AddCommGroup A]
    {n : Nat} (z : A) (hz : 2 • z = 0)
    (p q : Equiv.Perm (Fin n)) : A :=
  zmod2ToA z hz (schurCocycle p q)

@[simp]
theorem schurCocycleWith_one_left {A : Type*} [AddCommGroup A]
    {n : Nat} (z : A) (hz : 2 • z = 0)
    (q : Equiv.Perm (Fin n)) :
    schurCocycleWith z hz (1 : Equiv.Perm (Fin n)) q = 0 := by
  simp [schurCocycleWith, schurCocycle_one_left]

@[simp]
theorem schurCocycleWith_one_right {A : Type*} [AddCommGroup A]
    {n : Nat} (z : A) (hz : 2 • z = 0)
    (p : Equiv.Perm (Fin n)) :
    schurCocycleWith z hz p 1 = 0 := by
  simp [schurCocycleWith, schurCocycle_one_right]

theorem schurWith_cocycle {A : Type*} [AddCommGroup A]
    {n : Nat} (z : A) (hz : 2 • z = 0)
    (p q r : Equiv.Perm (Fin n)) :
    schurCocycleWith z hz p q +
        schurCocycleWith z hz (p * q) r =
      schurCocycleWith z hz q r +
        schurCocycleWith z hz p (q * r) := by
  unfold schurCocycleWith
  have h := schurCocycle_cocycle p q r
  calc
    zmod2ToA z hz (schurCocycle p q) +
        zmod2ToA z hz (schurCocycle (p * q) r) =
      zmod2ToA z hz
          (schurCocycle p q + schurCocycle (p * q) r) := by
      rw [map_add]
    _ = zmod2ToA z hz
          (schurCocycle q r + schurCocycle p (q * r)) := by
      rw [h]
    _ = zmod2ToA z hz (schurCocycle q r) +
          zmod2ToA z hz (schurCocycle p (q * r)) := by
      rw [map_add]

theorem schurWith_naturality {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] {n : Nat} (zA : A) (hzA : 2 • zA = 0)
    (zB : B) (hzB : 2 • zB = 0) (f : A →+ B)
    (hf : f zA = zB) (p q : Equiv.Perm (Fin n)) :
    f (schurCocycleWith zA hzA p q) =
      schurCocycleWith zB hzB p q := by
  unfold schurCocycleWith
  have key : ∀ c : ZMod 2,
      f (zmod2ToA zA hzA c) = zmod2ToA zB hzB c := by
    intro c
    have hc := zmod2_eq_zero_or_one c
    rcases hc with rfl | rfl
    · have h0A : zmod2ToA zA hzA 0 = 0 := by
        change (if (0 : ZMod 2) = 0 then (0 : A) else zA) = 0
        rw [ite_eq_left rfl]
      have h0B : zmod2ToA zB hzB 0 = 0 := by
        change (if (0 : ZMod 2) = 0 then (0 : B) else zB) = 0
        rw [ite_eq_left rfl]
      rw [h0A, h0B, map_zero]
    · have h1n : (1 : ZMod 2) ≠ 0 := by decide
      have hA1 : zmod2ToA zA hzA 1 = zA := by
        change (if (1 : ZMod 2) = 0 then (0 : A) else zA) = zA
        rw [ite_eq_right h1n]
      have hB1 : zmod2ToA zB hzB 1 = zB := by
        change (if (1 : ZMod 2) = 0 then (0 : B) else zB) = zB
        rw [ite_eq_right h1n]
      rw [hA1, hB1, hf]
  exact key (schurCocycle p q)

/-- The normalized Schur cocycle with the specified two-torsion coefficient. -/
noncomputable def schurNormalizedCocycleWith (A : Type*)
    [AddCommGroup A] (z : A) (hz : 2 • z = 0) (n : Nat) :
    NormalizedCocycleExtension.NormalizedCocycle
      (Equiv.Perm (Fin n)) (Multiplicative A) where
  cocycle p q :=
    Multiplicative.ofAdd (schurCocycleWith z hz p q)
  one_left := by
    intro q
    simp [schurCocycleWith_one_left]
  one_right := by
    intro p
    simp [schurCocycleWith_one_right]
  cocycle_assoc := by
    intro p q r
    have h := schurWith_cocycle z hz p q r
    calc
      Multiplicative.ofAdd (schurCocycleWith z hz p q) *
          Multiplicative.ofAdd
            (schurCocycleWith z hz (p * q) r) =
        Multiplicative.ofAdd
          (schurCocycleWith z hz p q +
            schurCocycleWith z hz (p * q) r) := by
        rw [← ofAdd_add]
      _ = Multiplicative.ofAdd
            (schurCocycleWith z hz q r +
              schurCocycleWith z hz p (q * r)) := by
        rw [h]
      _ = Multiplicative.ofAdd
              (schurCocycleWith z hz p (q * r)) *
            Multiplicative.ofAdd
              (schurCocycleWith z hz q r) := by
        rw [ofAdd_add, mul_comm]

section AdjacentSwap

variable {n : Nat}

theorem adjSwap_ne {i j : Fin n} (h : j.val = i.val + 1) : i ≠ j := by
  intro heq
  have hv : i.val = j.val := congrArg Fin.val heq
  rw [h] at hv
  omega

theorem adjSwap_lt {i j : Fin n} (h : j.val = i.val + 1) : i < j := by
  exact Fin.lt_def.mpr (by rw [h]; exact Nat.lt_succ_self _)

theorem swap_inv_eq_self {i j : Fin n} :
    (Equiv.swap i j : Equiv.Perm (Fin n))⁻¹ = Equiv.swap i j := by
  have hm : (Equiv.swap i j : Equiv.Perm (Fin n)) * Equiv.swap i j = 1 := by
    apply Equiv.Perm.ext
    intro k
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      Equiv.swap_apply_self]
  let s := (Equiv.swap i j : Equiv.Perm (Fin n))
  calc s⁻¹ = s⁻¹ * 1 := by simp
    _ = s⁻¹ * (s * s) := by rw [hm]
    _ = (s⁻¹ * s) * s := by rw [mul_assoc]
    _ = 1 * s := by rw [inv_mul_cancel]
    _ = s := by simp

theorem swap_inv_apply {i j : Fin n} (k : Fin n) :
    (Equiv.swap i j : Equiv.Perm (Fin n))⁻¹ k = Equiv.swap i j k := by
  rw [swap_inv_eq_self]

/-- The transposition of the two specified natural-number indices. -/
def natSwap (x y k : Nat) : Nat :=
  if k = x then y else if k = y then x else k

theorem natSwap_preserve {x y p q : Nat} (_hy : y = x + 1) (hpq : p < q)
    (hne : ¬(p = x ∧ q = y)) : natSwap x y p < natSwap x y q := by
  unfold natSwap
  by_cases hp_x : p = x
  · rw [ite_eq_left hp_x]
    by_cases hq_y : q = y
    · exfalso; exact hne ⟨hp_x, hq_y⟩
    · by_cases hq_x : q = x
      · omega
      · rw [ite_eq_right hq_x, ite_eq_right hq_y]; omega
  · rw [ite_eq_right hp_x]
    by_cases hp_y : p = y
    · rw [ite_eq_left hp_y]
      by_cases hq_x : q = x
      · omega
      · by_cases hq_y : q = y
        · omega
        · rw [ite_eq_right hq_x, ite_eq_right hq_y]; omega
    · rw [ite_eq_right hp_y]
      by_cases hq_x : q = x
      · rw [ite_eq_left hq_x]; omega
      · rw [ite_eq_right hq_x]
        by_cases hq_y : q = y
        · rw [ite_eq_left hq_y]; omega
        · rw [ite_eq_right hq_y]; exact hpq

theorem swap_adj_apply_val {i j : Fin n} (a : Fin n) :
    (Equiv.swap i j a).val = natSwap i.val j.val a.val := by
  unfold natSwap
  by_cases ha_i : a = i
  · have hv : a.val = i.val := congrArg Fin.val ha_i
    calc (Equiv.swap i j a).val = (Equiv.swap i j i).val := by rw [ha_i]
      _ = j.val := by rw [Equiv.swap_apply_left]
      _ = natSwap i.val j.val a.val := by simp [natSwap, hv]
  · by_cases ha_j : a = j
    · have hv : a.val = j.val := congrArg Fin.val ha_j
      have hv_not_i : a.val ≠ i.val := fun heq => ha_i (Fin.ext heq)
      have h_nat : natSwap i.val j.val a.val = i.val := by
        calc natSwap i.val j.val a.val
            = if a.val = i.val then j.val
              else if a.val = j.val then i.val else a.val := rfl
          _ = if a.val = j.val then i.val else a.val := by
              rw [ite_eq_right hv_not_i]
          _ = i.val := by rw [ite_eq_left hv]
      calc (Equiv.swap i j a).val = (Equiv.swap i j j).val := by rw [ha_j]
        _ = i.val := by rw [Equiv.swap_apply_right]
        _ = natSwap i.val j.val a.val := h_nat.symm
    · have hv_not_i : a.val ≠ i.val := fun heq => ha_i (Fin.ext heq)
      have hv_not_j : a.val ≠ j.val := fun heq => ha_j (Fin.ext heq)
      have hswap : Equiv.swap i j a = a :=
        Equiv.swap_apply_of_ne_of_ne ha_i ha_j
      calc (Equiv.swap i j a).val = a.val := by rw [hswap]
        _ = natSwap i.val j.val a.val := by
            simp [natSwap, hv_not_i, hv_not_j]

theorem swap_adj_preserve {i j : Fin n} (h : j.val = i.val + 1) {a b : Fin n}
    (hab : a < b) (hne : ¬(a = i ∧ b = j)) :
    Equiv.swap i j a < Equiv.swap i j b := by
  have hab_val : a.val < b.val := Fin.lt_def.mp hab
  have hne_val : ¬(a.val = i.val ∧ b.val = j.val) := fun ⟨hp, hq⟩ => hne ⟨Fin.ext hp, Fin.ext hq⟩
  have h_nat : natSwap i.val j.val a.val < natSwap i.val j.val b.val :=
    natSwap_preserve h hab_val hne_val
  have ha : (Equiv.swap i j a).val = natSwap i.val j.val a.val := swap_adj_apply_val a
  have hb : (Equiv.swap i j b).val = natSwap i.val j.val b.val := swap_adj_apply_val b
  exact Fin.lt_def.mpr (by rw [ha, hb]; exact h_nat)

theorem rootPerm_swap_adj_fixed {i j : Fin n} (h : j.val = i.val + 1) :
    rootPerm (Equiv.swap i j) (mkRoot i j (adjSwap_ne h)) = mkRoot i j (adjSwap_ne h) := by
  have hi_lt_j : i < j := adjSwap_lt h
  have hr0_eq : mkRoot i j (adjSwap_ne h) = (⟨(i, j), hi_lt_j⟩ : Root n) := by
    apply Subtype.ext
    simp [mkRoot, min_eq_left hi_lt_j.le, max_eq_right hi_lt_j.le]
  have hval : ((rootPerm (Equiv.swap i j) (⟨(i, j), hi_lt_j⟩ : Root n))).val =
      (i, j) := by
    change ((mkRoot (Equiv.swap i j i) (Equiv.swap i j j)
      ((Equiv.swap i j).injective.ne (adjSwap_ne h))) : Root n).val =
      (i, j)
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp [mkRoot, min_eq_right hi_lt_j.le, max_eq_left hi_lt_j.le]
  have hmid : rootPerm (Equiv.swap i j) (⟨(i, j), hi_lt_j⟩ : Root n) =
      (⟨(i, j), hi_lt_j⟩ : Root n) :=
    Subtype.ext hval
  rw [hr0_eq]
  exact hmid

theorem rootSignBit_swap_adj {i j : Fin n} (h : j.val = i.val + 1) (r : Root n) :
    rootSignBit (Equiv.swap i j) r = if r = mkRoot i j (adjSwap_ne h) then 1 else 0 := by
  have hi_lt_j : i < j := adjSwap_lt h
  let r0 := mkRoot i j (adjSwap_ne h)
  have hr0 : r0 = (⟨(i, j), hi_lt_j⟩ : Root n) := by
    apply Subtype.ext
    simp [r0, mkRoot, min_eq_left hi_lt_j.le, max_eq_right hi_lt_j.le]
  have h_inv : ∀ k : Fin n, (Equiv.swap i j : Equiv.Perm (Fin n))⁻¹ k = Equiv.swap i j k :=
    swap_inv_apply
  have h_bit : ∀ r : Root n, rootSignBit (Equiv.swap i j) r =
      if Equiv.swap i j r.1.1 < Equiv.swap i j r.1.2 then 0 else 1 := by
    intro r; unfold rootSignBit; rw [h_inv r.1.1, h_inv r.1.2]
  by_cases hr : r = r0
  · subst hr
    have ha : (r0 : Root n).1.1 = i := by rw [hr0]
    have hb : (r0 : Root n).1.2 = j := by rw [hr0]
    have hr0_eq : r0 = mkRoot i j (adjSwap_ne h) := rfl
    have not_lt : ¬(j < i) := not_lt.mpr hi_lt_j.le
    calc rootSignBit (Equiv.swap i j) r0
        = if Equiv.swap i j i < Equiv.swap i j j then 0 else 1 := by rw [h_bit r0, ha, hb]
      _ = if j < i then 0 else 1 := by rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      _ = 1 := by simp [not_lt]
      _ = if r0 = mkRoot i j (adjSwap_ne h) then 1 else 0 := by simp [hr0_eq]
  · have h_not_pair : ¬(r.1.1 = i ∧ r.1.2 = j) := by
      intro ⟨h1, h2⟩
      apply hr
      apply Subtype.ext
      rw [hr0]
      exact Prod.ext h1 h2
    have h_lt : Equiv.swap i j r.1.1 < Equiv.swap i j r.1.2 := swap_adj_preserve h r.2 h_not_pair
    rw [h_bit r, ite_eq_left h_lt, ite_eq_right hr]

theorem parityBit_swap_adj {i j : Fin n} (h : j.val = i.val + 1) :
    parityBit (Equiv.swap i j : Equiv.Perm (Fin n)) = 1 := by
  have hi_ne_j : i ≠ j := adjSwap_ne h
  have h_sign : Equiv.Perm.sign (Equiv.swap i j) = -1 := Equiv.Perm.sign_swap hi_ne_j
  have h_ne_one : Equiv.Perm.sign (Equiv.swap i j) ≠ 1 := by rw [h_sign]; decide
  unfold parityBit
  have h_unit :
      PermutationBilinearTitsAction.parityUnit
        (Multiplicative.ofAdd (1 : ZMod 2))
        (Equiv.swap i j) =
        Multiplicative.ofAdd (1 : ZMod 2) :=
    PermutationBilinearTitsAction.parityUnit_eq_eps_of_sign_ne_one h_ne_one
  rw [h_unit]
  rfl

theorem bitBicharacter_eval_ofAdd (a b : ZMod 2) :
    bitBicharacter.eval (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) = a * b := by
  unfold bitBicharacter SkewBicharacter.eval
  simp

theorem bitBicharacter_eval_rootSign {p : Equiv.Perm (Fin n)} (r1 r2 : Root n) :
    bitBicharacter.eval (rootSign p r1) (rootSign p r2) =
      rootSignBit p r1 * rootSignBit p r2 := by
  unfold rootSign
  rw [bitBicharacter_eval_ofAdd]

theorem lowerSum_singleton_one {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (b : SkewBicharacter (Multiplicative (ZMod 2)) (ZMod 2)) (r0 : ι)
    (u v : ι → Multiplicative (ZMod 2))
    (h : ∀ i j, b.eval (u i) (v j) = if i = r0 ∧ j = r0 then 1 else 0) :
    lowerSum b u v = 1 := by
  classical
  unfold lowerSum
  have h_inner : ∀ i : ι,
      (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), b.eval (u i) (v j)) =
        if i = r0 then 1 else 0 := by
    intro i
    by_cases hi : i = r0
    · have h_eq : ∀ j ∈ Finset.univ.filter (fun j => j ≤ r0),
          b.eval (u r0) (v j) = if j = r0 then 1 else 0 := by
        intro j _
        rw [h r0 j]
        by_cases hj : j = r0 <;> simp [hj]
      have h_sum : (∑ j ∈ Finset.univ.filter (fun j => j ≤ r0), b.eval (u r0) (v j)) =
          ∑ j ∈ Finset.univ.filter (fun j => j ≤ r0), if j = r0 then (1 : ZMod 2) else 0 :=
        Finset.sum_congr rfl h_eq
      have h_mem : r0 ∈ Finset.univ.filter (fun j : ι => j ≤ r0) := by simp
      have h_goal : (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), b.eval (u i) (v j)) = 1 := by
        calc (∑ j ∈ Finset.univ.filter (fun j => j ≤ i), b.eval (u i) (v j))
            = (∑ j ∈ Finset.univ.filter (fun j => j ≤ r0), b.eval (u r0) (v j)) := by rw [hi]
          _ = ∑ j ∈ Finset.univ.filter (fun j => j ≤ r0),
              if j = r0 then (1 : ZMod 2) else 0 := h_sum
          _ = 1 := by
              rw [Finset.sum_ite_eq' _ r0 (fun _ => (1 : ZMod 2)), ite_eq_left h_mem]
      rw [h_goal, ite_eq_left hi]
    · have h_zero : ∀ j ∈ Finset.univ.filter (fun j => j ≤ i),
          b.eval (u i) (v j) = 0 := by
        intro j _
        rw [h i j]
        simp [hi]
      rw [Finset.sum_eq_zero h_zero, ite_eq_right hi]
  calc (∑ i : ι, ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), b.eval (u i) (v j))
      = ∑ i : ι, if i = r0 then (1 : ZMod 2) else 0 :=
        Finset.sum_congr rfl (fun i _ => h_inner i)
    _ = 1 := by
        have : (∑ i : ι, if i = r0 then (1 : ZMod 2) else 0) =
            ∑ i ∈ Finset.univ, if i = r0 then (1 : ZMod 2) else 0 := rfl
        rw [this, Finset.sum_ite_eq' Finset.univ r0 (fun _ => (1 : ZMod 2))]
        simp

theorem inversionSum_singleton_zero {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    (b : SkewBicharacter (Multiplicative (ZMod 2)) (ZMod 2))
    (σ : Equiv.Perm ι) (r0 : ι) (u : ι → Multiplicative (ZMod 2))
    (h : ∀ i j, b.eval (u i) (u j) = if i = r0 ∧ j = r0 then 1 else 0) :
    inversionSum b σ u = 0 := by
  classical
  unfold inversionSum
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hj_lt : i < j := (Finset.mem_filter.mp hj).2.1
  rw [h i j]
  by_cases hi : i = r0
  · by_cases hj2 : j = r0
    · subst hj2; rw [hi] at hj_lt; simp at hj_lt
    · simp [hi, hj2]
  · simp [hi]

theorem rootCocycle0_swap_adj_self {i j : Fin n} (h : j.val = i.val + 1) :
    rootCocycle0 (Equiv.swap i j) (Equiv.swap i j) = 1 := by
  classical
  let s := Equiv.swap i j
  let r0 := mkRoot i j (adjSwap_ne h)
  have h_bit : ∀ r, rootSignBit s r = if r = r0 then 1 else 0 := rootSignBit_swap_adj h
  have h_fixed : rootPerm s r0 = r0 := rootPerm_swap_adj_fixed h
  have h_inv_fixed : (rootPerm s)⁻¹ r0 = r0 := by
    have h1 := (rootPerm s).symm_apply_apply r0
    rw [h_fixed] at h1
    exact h1
  have h_inv_eq : ∀ r, (rootPerm s)⁻¹ r = r0 ↔ r = r0 := by
    intro r
    constructor
    · intro hr
      have : rootPerm s ((rootPerm s)⁻¹ r) = r := by simp
      rw [hr, h_fixed] at this
      exact this.symm
    · intro hr
      rw [hr, h_inv_fixed]
  have h_bit_perm : ∀ r, rootSignBit s ((rootPerm s)⁻¹ r) = if r = r0 then 1 else 0 := by
    intro r
    rw [h_bit ((rootPerm s)⁻¹ r)]
    by_cases hr : r = r0
    · rw [ite_eq_left hr, ite_eq_left (by rw [hr, h_inv_fixed])]
    · rw [ite_eq_right hr, ite_eq_right (fun heq => hr ((h_inv_eq r).mp heq))]
  have h_eval_lower : ∀ a b : Root n,
      bitBicharacter.eval (rootSign s a) (permute (rootPerm s) (rootSign s) b) =
        if a = r0 ∧ b = r0 then 1 else 0 := by
    intro a b
    have hp : permute (rootPerm s) (rootSign s) b = rootSign s ((rootPerm s)⁻¹ b) := rfl
    rw [hp, bitBicharacter_eval_rootSign, h_bit a, h_bit_perm b]
    by_cases ha : a = r0 <;> by_cases hb : b = r0 <;> simp [ha, hb]
  have h_eval_inv : ∀ a b : Root n,
      bitBicharacter.eval (rootSign s a) (rootSign s b) =
        if a = r0 ∧ b = r0 then 1 else 0 := by
    intro a b
    rw [bitBicharacter_eval_rootSign, h_bit a, h_bit b]
    by_cases ha : a = r0 <;> by_cases hb : b = r0 <;> simp [ha, hb]
  have h_lower : lowerSum bitBicharacter (rootSign s)
      (permute (rootPerm s) (rootSign s)) = 1 :=
    lowerSum_singleton_one bitBicharacter r0 (rootSign s)
      (permute (rootPerm s) (rootSign s)) h_eval_lower
  have h_inv : inversionSum bitBicharacter (rootPerm s) (rootSign s) = 0 :=
    inversionSum_singleton_zero bitBicharacter (rootPerm s) r0 (rootSign s) h_eval_inv
  have h_root : rootCocycle0 s s =
      lowerSum bitBicharacter (rootSign s) (permute (rootPerm s) (rootSign s)) +
        inversionSum bitBicharacter (rootPerm s) (rootSign s) := by
    calc rootCocycle0 s s
        = monomialAddCocycle bitBicharacter (rootMonomial n s) (rootMonomial n s) := rfl
      _ = lowerSum bitBicharacter (rootMonomial n s).left
            (permute (rootMonomial n s).right (rootMonomial n s).left) +
          inversionSum bitBicharacter (rootMonomial n s).right (rootMonomial n s).left := rfl
      _ = lowerSum bitBicharacter (rootSign s) (permute (rootPerm s) (rootSign s)) +
          inversionSum bitBicharacter (rootPerm s) (rootSign s) := by rfl
  rw [h_root, h_lower, h_inv, add_zero]

theorem schurCocycle_swap_adj_self {i j : Fin n} (h : j.val = i.val + 1) :
    schurCocycle (Equiv.swap i j) (Equiv.swap i j) = 0 := by
  have h_root := rootCocycle0_swap_adj_self h
  have h_par := parityBit_swap_adj h
  unfold schurCocycle
  rw [h_root, h_par]
  have h_two : (2 : ZMod 2) = 0 := ZMod.natCast_eq_zero_iff_even.mpr ⟨1, rfl⟩
  calc (1 : ZMod 2) + 1 * 1 = 1 + 1 := by ring
    _ = 2 := by rw [one_add_one_eq_two]
    _ = 0 := h_two

end AdjacentSwap

section GeneralTransposition

variable {n : Nat}

private theorem zmod2MulSelf (a : Multiplicative (ZMod 2)) :
    a * a = 1 := by
  apply Multiplicative.toAdd.injective
  change a.toAdd + a.toAdd = 0
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc a.toAdd + a.toAdd = 2 * a.toAdd := by ring
    _ = 0 := by rw [h2, zero_mul]

private noncomputable def cocycleLift (p : Equiv.Perm (Fin n)) :
    NormalizedCocycleExtension.Extension (schurNormalizedCocycle n) :=
  ⟨p, 1⟩

private theorem cocycleLift_sq_of_zero (p : Equiv.Perm (Fin n))
    (hp : p * p = 1) (hc : schurCocycle p p = 0) :
    cocycleLift (n := n) p * cocycleLift (n := n) p = 1 := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact hp
  · change (1 : Multiplicative (ZMod 2)) * 1 *
        Multiplicative.ofAdd (schurCocycle p p) = 1
    rw [hc]
    rfl

private theorem schurCocycle_conj_eq_zero (p e t : Equiv.Perm (Fin n))
    (hp : p * p = 1) (hc : schurCocycle p p = 0)
    (ht : e * p * e⁻¹ = t) : schurCocycle t t = 0 := by
  let x : NormalizedCocycleExtension.Extension
      (schurNormalizedCocycle n) := cocycleLift (n := n) p
  let g : NormalizedCocycleExtension.Extension
      (schurNormalizedCocycle n) := cocycleLift (n := n) e
  let y := g * x * g⁻¹
  have hx : x * x = 1 :=
    cocycleLift_sq_of_zero (n := n) p hp hc
  have hy : y * y = 1 := by
    calc y * y = g * (x * x) * g⁻¹ := by dsimp [y]; group
      _ = 1 := by rw [hx]; simp
  have hybase : y.base = t := by
    dsimp [y, g, x, cocycleLift]
    exact ht
  have hcoeff := congrArg
    NormalizedCocycleExtension.Extension.coeff hy
  change y.coeff * y.coeff *
      (schurNormalizedCocycle n).cocycle y.base y.base = 1 at hcoeff
  rw [hybase] at hcoeff
  have hsq : y.coeff * y.coeff = 1 := zmod2MulSelf y.coeff
  rw [hsq, one_mul] at hcoeff
  have h := hcoeff
  simp only [schurNormalizedCocycle, schurCocycleMul] at h
  exact Multiplicative.ofAdd.injective h

private theorem schurCocycle_swap_self_of_lt {i j : Fin n}
    (hij : i < j) :
    schurCocycle (Equiv.swap i j) (Equiv.swap i j) = 0 := by
  let k : Fin n :=
    ⟨i.val + 1, lt_of_le_of_lt (Nat.succ_le_iff.mpr hij) j.isLt⟩
  have hk : k.val = i.val + 1 := rfl
  have hik : i ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [k] at hv
    omega
  let e : Equiv.Perm (Fin n) := Equiv.swap k j
  have hei : e i = i := by
    dsimp [e]
    rw [Equiv.swap_apply_of_ne_of_ne hik hij.ne]
  have hek : e k = j := by
    dsimp [e]
    rw [Equiv.swap_apply_left]
  have hconj : e * Equiv.swap i k * e⁻¹ = Equiv.swap i j := by
    have h := Equiv.symm_trans_swap_trans i k e
    change e * Equiv.swap i k * e⁻¹ =
      Equiv.swap (e i) (e k) at h
    rw [hei, hek] at h
    exact h
  exact schurCocycle_conj_eq_zero (p := Equiv.swap i k) (e := e)
    (t := Equiv.swap i j) (Equiv.swap_mul_self i k)
    (schurCocycle_swap_adj_self hk) hconj

theorem schurCocycle_swap_self {i j : Fin n} (hij : i ≠ j) :
    schurCocycle (Equiv.swap i j) (Equiv.swap i j) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact schurCocycle_swap_self_of_lt hlt
  · have h := schurCocycle_swap_self_of_lt (i := j) (j := i) hgt
    simpa [Equiv.swap_comm] using h

theorem schurCocycleWith_swap_self {A : Type*} [AddCommGroup A]
    {i j : Fin n} (hij : i ≠ j) (z : A) (hz : 2 • z = 0) :
    schurCocycleWith z hz (Equiv.swap i j) (Equiv.swap i j) = 0 := by
  have h0 := schurCocycle_swap_self hij
  simp [schurCocycleWith, h0]

end GeneralTransposition

section AdjacentOverlap

variable {n : Nat}

/-- Orientation bits compose additively, with the inner bit evaluated at the
root pulled back through the outer root permutation. -/
theorem rootSignBit_mul {p q : Equiv.Perm (Fin n)}
    (r : Root n) :
    rootSignBit (p * q) r =
      rootSignBit p r + rootSignBit q ((rootPerm p)⁻¹ r) := by
  have h := rootSign_mul (n := n) p q
  have h1 : rootSign (p * q) r =
      rootSign p r * permute (rootPerm p) (rootSign q) r := by
    rw [h]
    rfl
  change Multiplicative.ofAdd (rootSignBit (p * q) r) =
      Multiplicative.ofAdd (rootSignBit p r) *
        Multiplicative.ofAdd (rootSignBit q ((rootPerm p)⁻¹ r)) at h1
  have h2 : Multiplicative.ofAdd
      (rootSignBit p r + rootSignBit q ((rootPerm p)⁻¹ r)) =
      Multiplicative.ofAdd (rootSignBit p r) *
        Multiplicative.ofAdd (rootSignBit q ((rootPerm p)⁻¹ r)) := by
    rw [← ofAdd_add]
  rw [← h2] at h1
  exact Multiplicative.ofAdd.injective h1

private theorem sum_rootSignBit_mul (p q : Equiv.Perm (Fin n)) :
    (∑ r : Root n, rootSignBit (p * q) r) =
      (∑ r : Root n, rootSignBit p r) +
        ∑ r : Root n, rootSignBit q r := by
  classical
  have h1 : ∀ r : Root n, rootSignBit (p * q) r =
      rootSignBit p r + rootSignBit q ((rootPerm p)⁻¹ r) :=
    rootSignBit_mul
  conv_lhs => arg 2; ext r; rw [h1 r]
  rw [Finset.sum_add_distrib]
  congr 1
  have h2 : (∑ r : Root n, rootSignBit q ((rootPerm p)⁻¹ r)) =
      ∑ r : Root n, rootSignBit q r := by
    calc ∑ r : Root n, rootSignBit q ((rootPerm p)⁻¹ r)
        = ∑ r : Root n, rootSignBit q ((rootPerm p).symm r) := rfl
      _ = ∑ r : Root n, rootSignBit q r :=
          Equiv.sum_comp (rootPerm p).symm
            (fun r => rootSignBit q r)
  exact h2

private theorem sum_rootSignBit_one :
    (∑ _r : Root n, rootSignBit (1 : Equiv.Perm (Fin n)) _r) = 0 := by
  classical
  have h : ∀ r : Root n, rootSignBit (1 : Equiv.Perm (Fin n)) r = 0 := by
    intro r
    unfold rootSignBit
    simp [r.2]
  simp [h]

private theorem sum_rootSignBit_swap_adj {i j : Fin n}
    (h : j.val = i.val + 1) :
    (∑ r : Root n, rootSignBit (Equiv.swap i j) r) = 1 := by
  classical
  have hbit : ∀ r : Root n, rootSignBit (Equiv.swap i j) r =
      if r = mkRoot i j (adjSwap_ne h) then 1 else 0 :=
    rootSignBit_swap_adj h
  have hsum : (∑ r : Root n, rootSignBit (Equiv.swap i j) r) =
      ∑ r : Root n,
        (if r = mkRoot i j (adjSwap_ne h) then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hbit r]
  rw [hsum,
    Finset.sum_ite_eq' Finset.univ (mkRoot i j (adjSwap_ne h))
      (fun _ => (1 : ZMod 2))]
  simp

private theorem sum_rootSignBit_inv (p : Equiv.Perm (Fin n)) :
    (∑ r : Root n, rootSignBit p⁻¹ r) =
      ∑ r : Root n, rootSignBit p r := by
  classical
  have hmul : (∑ r : Root n, rootSignBit (p * p⁻¹) r) = 0 := by
    rw [mul_inv_cancel, sum_rootSignBit_one]
  rw [sum_rootSignBit_mul p p⁻¹] at hmul
  have hchar : ∀ x : ZMod 2, x + x = 0 := by
    intro x
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc x + x = 2 * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  have h1 : (∑ r, rootSignBit p r) +
      (∑ r, rootSignBit p⁻¹ r) = 0 := hmul
  have h2 : (∑ r, rootSignBit p r) +
      (∑ r, rootSignBit p r) = 0 := hchar _
  calc (∑ r, rootSignBit p⁻¹ r)
      = (∑ r, rootSignBit p⁻¹ r) + 0 := by rw [add_zero]
    _ = (∑ r, rootSignBit p⁻¹ r) +
        ((∑ r, rootSignBit p r) + (∑ r, rootSignBit p r)) := by
        rw [h2]
    _ = ((∑ r, rootSignBit p⁻¹ r) + (∑ r, rootSignBit p r)) +
        (∑ r, rootSignBit p r) := by ring
    _ = 0 + (∑ r, rootSignBit p r) := by
        rw [add_comm (∑ r, rootSignBit p⁻¹ r) (∑ r, rootSignBit p r), h1]
    _ = ∑ r, rootSignBit p r := by rw [zero_add]

private theorem sum_rootSignBit_conj (p q : Equiv.Perm (Fin n)) :
    (∑ r, rootSignBit (p * q * p⁻¹) r) =
      ∑ r, rootSignBit q r := by
  classical
  have h1 : (∑ r, rootSignBit (p * q * p⁻¹) r) =
      (∑ r, rootSignBit p r) + (∑ r, rootSignBit q r) +
        (∑ r, rootSignBit p⁻¹ r) := by
    rw [sum_rootSignBit_mul, sum_rootSignBit_mul]
  rw [h1, sum_rootSignBit_inv p]
  have hchar : ∀ x : ZMod 2, x + x = 0 := by
    intro x
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc x + x = 2 * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  calc (∑ r, rootSignBit p r) + (∑ r, rootSignBit q r) +
        (∑ r, rootSignBit p r)
      = (∑ r, rootSignBit q r) +
        ((∑ r, rootSignBit p r) + (∑ r, rootSignBit p r)) := by ring
    _ = (∑ r, rootSignBit q r) + 0 := by rw [hchar]
    _ = ∑ r, rootSignBit q r := by rw [add_zero]

private theorem sum_rootSignBit_swap_aux {a b : Fin n}
    (h : a < b) :
    (∑ r : Root n, rootSignBit (Equiv.swap a b) r) = 1 := by
  classical
  have hv : a.val < b.val := Fin.lt_def.mp h
  have key : ∀ (d : Nat) (x y : Fin n), x < y →
      y.val - x.val = d →
      (∑ r : Root n, rootSignBit (Equiv.swap x y) r) = 1 := by
    intro d
    induction d using Nat.strongRecOn with
    | _ d ih =>
      intro x y hxy hd
      have hd_pos : 1 ≤ d := by omega
      by_cases hd_one : d = 1
      · have hadj : y.val = x.val + 1 := by omega
        exact sum_rootSignBit_swap_adj hadj
      · have hd_ge2 : 2 ≤ d := by omega
        let x' : Fin n := ⟨x.val + 1, by omega⟩
        have hx'_val : x'.val = x.val + 1 := rfl
        have hx_lt_x' : x < x' := by
          apply Fin.lt_def.mpr
          simp [x']
        have hx'_lt_y : x' < y := by
          apply Fin.lt_def.mpr
          simp [x']
          omega
        have hd' : y.val - x'.val = d - 1 := by omega
        have hm_lt : d - 1 < d := by omega
        have ih_x' : (∑ r, rootSignBit (Equiv.swap x' y) r) = 1 :=
          ih (d - 1) hm_lt x' y hx'_lt_y hd'
        let e : Equiv.Perm (Fin n) := Equiv.swap x x'
        have he_x' : e x' = x := by
          dsimp [e]
          rw [Equiv.swap_apply_right]
        have he_y : e y = y := by
          dsimp [e]
          have h1 : y ≠ x := Ne.symm (Fin.ne_of_lt hxy)
          have h2 : y ≠ x' := Ne.symm (Fin.ne_of_lt hx'_lt_y)
          exact Equiv.swap_apply_of_ne_of_ne h1 h2
        have swap_conj : ∀ (p : Equiv.Perm (Fin n)) (u v : Fin n),
            p * Equiv.swap u v * p⁻¹ = Equiv.swap (p u) (p v) := by
          intro p u v
          apply Equiv.Perm.ext
          intro z
          simp only [Equiv.Perm.mul_apply]
          by_cases hz_u : z = p u
          · have hp_inv_u : p⁻¹ z = u := by
              calc p⁻¹ z = p⁻¹ (p u) := by rw [hz_u]
                _ = u := by simp [Equiv.symm_apply_apply]
            rw [hp_inv_u, Equiv.swap_apply_left,
              hz_u, Equiv.swap_apply_left]
          · by_cases hz_v : z = p v
            · have hp_inv_v : p⁻¹ z = v := by
                calc p⁻¹ z = p⁻¹ (p v) := by rw [hz_v]
                  _ = v := by simp [Equiv.symm_apply_apply]
              rw [hp_inv_v, Equiv.swap_apply_right,
                hz_v, Equiv.swap_apply_right]
            · have hp_ne_u : p⁻¹ z ≠ u := by
                intro heq
                have : z = p u := by
                  calc z = p (p⁻¹ z) := by simp [Equiv.apply_symm_apply]
                    _ = p u := by rw [heq]
                exact hz_u this
              have hp_ne_v : p⁻¹ z ≠ v := by
                intro heq
                have : z = p v := by
                  calc z = p (p⁻¹ z) := by simp [Equiv.apply_symm_apply]
                    _ = p v := by rw [heq]
                exact hz_v this
              rw [Equiv.swap_apply_of_ne_of_ne hp_ne_u hp_ne_v,
                Equiv.swap_apply_of_ne_of_ne hz_u hz_v]
              simp [Equiv.apply_symm_apply]
        have h_swap_eq : Equiv.swap x y =
            e * Equiv.swap x' y * e⁻¹ := by
          calc Equiv.swap x y = Equiv.swap (e x') (e y) := by
                rw [he_x', he_y]
            _ = e * Equiv.swap x' y * e⁻¹ := by
                rw [swap_conj e x' y]
        have h_sum_conj : (∑ r, rootSignBit
            (e * Equiv.swap x' y * e⁻¹) r) =
            ∑ r, rootSignBit (Equiv.swap x' y) r :=
          sum_rootSignBit_conj e (Equiv.swap x' y)
        calc (∑ r, rootSignBit (Equiv.swap x y) r)
            = ∑ r, rootSignBit (e * Equiv.swap x' y * e⁻¹) r := by
                rw [← h_swap_eq]
          _ = ∑ r, rootSignBit (Equiv.swap x' y) r := h_sum_conj
          _ = 1 := ih_x'
  exact key (b.val - a.val) a b h rfl

private theorem sum_rootSignBit_swap_general {a b : Fin n}
    (h : a ≠ b) :
    (∑ r : Root n, rootSignBit (Equiv.swap a b) r) = 1 := by
  classical
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact sum_rootSignBit_swap_aux hlt
  · have hcomm : Equiv.swap a b = Equiv.swap b a :=
      Equiv.swap_comm a b
    rw [hcomm]
    exact sum_rootSignBit_swap_aux hgt
private theorem parityBit_swap_general {a b : Fin n} (h : a ≠ b) :
    parityBit (Equiv.swap a b) = 1 := by
  unfold parityBit
  have hsign : Equiv.Perm.sign (Equiv.swap a b) = -1 :=
    Equiv.Perm.sign_swap h
  have hne : Equiv.Perm.sign (Equiv.swap a b) ≠ 1 := by
    rw [hsign]
    decide
  have hunit :=
    PermutationBilinearTitsAction.parityUnit_eq_eps_of_sign_ne_one
      (eps := Multiplicative.ofAdd (1 : ZMod 2)) hne
  rw [hunit]
  rfl

private theorem parityBit_eq_sum_rootSignBit
    (p : Equiv.Perm (Fin n)) :
    parityBit p = ∑ r : Root n, rootSignBit p r := by
  classical
  induction p using Equiv.Perm.swap_induction_on with
  | one =>
    rw [parityBit_one, sum_rootSignBit_one]
  | swap_mul f x y hxy ih =>
    rw [parityBit_mul, sum_rootSignBit_mul, ih,
      parityBit_swap_general hxy, sum_rootSignBit_swap_general hxy]

private theorem rootPerm_mkRoot_pos {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_k_i : p k = i) (hp_l_j : p l = j) :
    rootPerm p (mkRoot k l (adjSwap_ne hkl)) =
      mkRoot i j (adjSwap_ne hij) := by
  have hk_lt_l : k < l := adjSwap_lt hkl
  have hi_lt_j : i < j := adjSwap_lt hij
  have hk_eq : mkRoot k l (adjSwap_ne hkl) = (⟨(k, l), hk_lt_l⟩ : Root n) := by
    apply Subtype.ext
    simp [mkRoot, min_eq_left hk_lt_l.le, max_eq_right hk_lt_l.le]
  calc rootPerm p (mkRoot k l (adjSwap_ne hkl))
      = rootPerm p ⟨(k, l), hk_lt_l⟩ := by rw [hk_eq]
    _ = mkRoot (p k) (p l) (p.injective.ne hk_lt_l.ne) := rfl
    _ = mkRoot i j (adjSwap_ne hij) := by
        apply Subtype.ext
        simp [mkRoot, hp_k_i, hp_l_j,
          min_eq_left hi_lt_j.le, max_eq_right hi_lt_j.le]

private theorem rootPerm_mkRoot_neg {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_l_i : p l = i) (hp_k_j : p k = j) :
    rootPerm p (mkRoot k l (adjSwap_ne hkl)) =
      mkRoot i j (adjSwap_ne hij) := by
  have hk_lt_l : k < l := adjSwap_lt hkl
  have hi_lt_j : i < j := adjSwap_lt hij
  have hk_eq : mkRoot k l (adjSwap_ne hkl) = (⟨(k, l), hk_lt_l⟩ : Root n) := by
    apply Subtype.ext
    simp [mkRoot, min_eq_left hk_lt_l.le, max_eq_right hk_lt_l.le]
  have h_min : min j i = i := min_eq_right hi_lt_j.le
  have h_max : max j i = j := max_eq_left hi_lt_j.le
  have h_min2 : min i j = i := min_eq_left hi_lt_j.le
  have h_max2 : max i j = j := max_eq_right hi_lt_j.le
  calc rootPerm p (mkRoot k l (adjSwap_ne hkl))
      = rootPerm p ⟨(k, l), hk_lt_l⟩ := by rw [hk_eq]
    _ = mkRoot (p k) (p l) (p.injective.ne hk_lt_l.ne) := rfl
    _ = mkRoot i j (adjSwap_ne hij) := by
        apply Subtype.ext
        simp only [mkRoot, hp_k_j, hp_l_i, h_min, h_max, h_min2, h_max2]

private theorem permute_rootSign_swap_pos {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_k_i : p k = i) (hp_l_j : p l = j)
    (r : Root n) :
    permute (rootPerm p) (rootSign (Equiv.swap k l)) r =
      if r = mkRoot i j (adjSwap_ne hij) then
        Multiplicative.ofAdd (1 : ZMod 2) else 1 := by
  have h_bit : ∀ s : Root n, rootSign (Equiv.swap k l) s =
      if s = mkRoot k l (adjSwap_ne hkl) then
        Multiplicative.ofAdd 1 else 1 := by
    intro s
    simp only [rootSign]
    have hb := rootSignBit_swap_adj hkl s
    rw [hb]
    by_cases hs : s = mkRoot k l (adjSwap_ne hkl)
    · simp [hs]
    · simp [hs]
  have h_perm : rootPerm p (mkRoot k l (adjSwap_ne hkl)) =
      mkRoot i j (adjSwap_ne hij) :=
    rootPerm_mkRoot_pos hij hkl p hp_k_i hp_l_j
  have h_inv : (rootPerm p)⁻¹ (mkRoot i j (adjSwap_ne hij)) =
      mkRoot k l (adjSwap_ne hkl) := by
    have h1 := (rootPerm p).symm_apply_apply
      (mkRoot k l (adjSwap_ne hkl))
    rw [h_perm] at h1
    exact h1
  have h_equiv : ∀ r : Root n,
      ((rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl)) ↔
        (r = mkRoot i j (adjSwap_ne hij)) := by
    intro r
    constructor
    · intro h
      calc r = rootPerm p ((rootPerm p)⁻¹ r) := by simp
        _ = rootPerm p (mkRoot k l (adjSwap_ne hkl)) := by rw [h]
        _ = mkRoot i j (adjSwap_ne hij) := h_perm
    · intro h
      rw [h, h_inv]
  calc permute (rootPerm p) (rootSign (Equiv.swap k l)) r
      = rootSign (Equiv.swap k l) ((rootPerm p)⁻¹ r) := rfl
    _ = if (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) then
          Multiplicative.ofAdd 1 else 1 := by
        rw [h_bit]
    _ = if r = mkRoot i j (adjSwap_ne hij) then
          Multiplicative.ofAdd 1 else 1 := by
        have h_if : (if (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl)
            then Multiplicative.ofAdd (1 : ZMod 2) else 1) =
            if r = mkRoot i j (adjSwap_ne hij) then
              Multiplicative.ofAdd 1 else 1 := by
          by_cases hr : r = mkRoot i j (adjSwap_ne hij)
          · have h1 : (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) :=
              (h_equiv r).mpr hr
            rw [ite_eq_left hr, ite_eq_left h1]
          · have h1 : ¬(rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) := by
              intro h
              exact hr ((h_equiv r).mp h)
            rw [ite_eq_right hr, ite_eq_right h1]
        exact h_if

private theorem permute_rootSign_swap_neg {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_l_i : p l = i) (hp_k_j : p k = j)
    (r : Root n) :
    permute (rootPerm p) (rootSign (Equiv.swap k l)) r =
      if r = mkRoot i j (adjSwap_ne hij) then
        Multiplicative.ofAdd (1 : ZMod 2) else 1 := by
  have h_bit : ∀ s : Root n, rootSign (Equiv.swap k l) s =
      if s = mkRoot k l (adjSwap_ne hkl) then
        Multiplicative.ofAdd 1 else 1 := by
    intro s
    simp only [rootSign]
    have hb := rootSignBit_swap_adj hkl s
    rw [hb]
    by_cases hs : s = mkRoot k l (adjSwap_ne hkl)
    · simp [hs]
    · simp [hs]
  have h_perm : rootPerm p (mkRoot k l (adjSwap_ne hkl)) =
      mkRoot i j (adjSwap_ne hij) :=
    rootPerm_mkRoot_neg hij hkl p hp_l_i hp_k_j
  have h_inv : (rootPerm p)⁻¹ (mkRoot i j (adjSwap_ne hij)) =
      mkRoot k l (adjSwap_ne hkl) := by
    have h1 := (rootPerm p).symm_apply_apply
      (mkRoot k l (adjSwap_ne hkl))
    rw [h_perm] at h1
    exact h1
  have h_equiv : ∀ r : Root n,
      ((rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl)) ↔
        (r = mkRoot i j (adjSwap_ne hij)) := by
    intro r
    constructor
    · intro h
      calc r = rootPerm p ((rootPerm p)⁻¹ r) := by simp
        _ = rootPerm p (mkRoot k l (adjSwap_ne hkl)) := by rw [h]
        _ = mkRoot i j (adjSwap_ne hij) := h_perm
    · intro h
      rw [h, h_inv]
  calc permute (rootPerm p) (rootSign (Equiv.swap k l)) r
      = rootSign (Equiv.swap k l) ((rootPerm p)⁻¹ r) := rfl
    _ = if (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) then
          Multiplicative.ofAdd 1 else 1 := by
        rw [h_bit]
    _ = if r = mkRoot i j (adjSwap_ne hij) then
          Multiplicative.ofAdd 1 else 1 := by
        have h_if : (if (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl)
            then Multiplicative.ofAdd (1 : ZMod 2) else 1) =
            if r = mkRoot i j (adjSwap_ne hij) then
              Multiplicative.ofAdd 1 else 1 := by
          by_cases hr : r = mkRoot i j (adjSwap_ne hij)
          · have h1 : (rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) :=
              (h_equiv r).mpr hr
            rw [ite_eq_left hr, ite_eq_left h1]
          · have h1 : ¬(rootPerm p)⁻¹ r = mkRoot k l (adjSwap_ne hkl) := by
              intro h
              exact hr ((h_equiv r).mp h)
            rw [ite_eq_right hr, ite_eq_right h1]
        exact h_if

private theorem inversionSum_rootPerm_swap_zero {n : Nat}
    (p : Equiv.Perm (Fin n)) {k l : Fin n} (hkl : l.val = k.val + 1) :
    inversionSum bitBicharacter (rootPerm p)
        (rootSign (Equiv.swap k l)) = 0 := by
  classical
  have h_eval : ∀ a b : Root n,
      bitBicharacter.eval (rootSign (Equiv.swap k l) a)
        (rootSign (Equiv.swap k l) b) =
        if a = mkRoot k l (adjSwap_ne hkl) ∧
            b = mkRoot k l (adjSwap_ne hkl) then 1 else 0 := by
    intro a b
    rw [bitBicharacter_eval_rootSign, rootSignBit_swap_adj hkl a,
      rootSignBit_swap_adj hkl b]
    by_cases ha : a = mkRoot k l (adjSwap_ne hkl) <;>
      by_cases hb : b = mkRoot k l (adjSwap_ne hkl) <;> simp [ha, hb]
  exact inversionSum_singleton_zero bitBicharacter (rootPerm p)
    (mkRoot k l (adjSwap_ne hkl)) (rootSign (Equiv.swap k l)) h_eval

private theorem rootSign_swap_adj_delta {n : Nat} {i j : Fin n}
    (h : j.val = i.val + 1) (r : Root n) :
    (rootSign (Equiv.swap i j) r).toAdd =
      if r = mkRoot i j (adjSwap_ne h) then 1 else 0 := by
  have hbit := rootSignBit_swap_adj h r
  unfold rootSign
  rw [hbit]
  by_cases hr : r = mkRoot i j (adjSwap_ne h)
  · simp [hr]
  · simp [hr]

private theorem lowerSum_rootSign_perm_swap {n : Nat}
    {i j k l : Fin n} (hij : j.val = i.val + 1)
    (hkl : l.val = k.val + 1) (p : Equiv.Perm (Fin n))
    (hp_k_i : p k = i) (hp_l_j : p l = j) :
    lowerSum bitBicharacter (rootSign p)
        (permute (rootPerm p) (rootSign (Equiv.swap k l))) =
      ∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
        rootSignBit p r else 0 := by
  classical
  let r0 := mkRoot i j (adjSwap_ne hij)
  have h_perm : ∀ r : Root n,
      permute (rootPerm p) (rootSign (Equiv.swap k l)) r =
        if r = r0 then Multiplicative.ofAdd 1 else 1 :=
    permute_rootSign_swap_pos hij hkl p hp_k_i hp_l_j
  have h_toAdd : ∀ r : Root n,
      (permute (rootPerm p) (rootSign (Equiv.swap k l)) r).toAdd =
        if r = r0 then 1 else 0 := by
    intro r
    rw [h_perm r]
    by_cases hr : r = r0
    · simp [hr]
    · simp [hr]
  unfold lowerSum
  have h_eval : ∀ (a : Root n) (b : Root n),
      bitBicharacter.eval (rootSign p a)
        (permute (rootPerm p) (rootSign (Equiv.swap k l)) b) =
        rootSignBit p a *
          (permute (rootPerm p) (rootSign (Equiv.swap k l)) b).toAdd := by
    intro a b
    have ha : rootSign p a = Multiplicative.ofAdd (rootSignBit p a) := rfl
    by_cases hb : b = r0
    · have hb1 : permute (rootPerm p) (rootSign (Equiv.swap k l)) b =
          Multiplicative.ofAdd 1 := by rw [h_perm b, ite_eq_left hb]
      have h_left : bitBicharacter.eval (rootSign p a)
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) b) =
            rootSignBit p a * 1 := by
        rw [ha, hb1, bitBicharacter_eval_ofAdd]
      have h_right : rootSignBit p a *
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) b).toAdd =
            rootSignBit p a * 1 := by
        rw [h_toAdd b, ite_eq_left hb]
      rw [h_left, h_right]
    · have hb1 : permute (rootPerm p) (rootSign (Equiv.swap k l)) b = 1 := by
        rw [h_perm b, ite_eq_right hb]
      have h1 : (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 0 := rfl
      have h_left : bitBicharacter.eval (rootSign p a)
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) b) =
            rootSignBit p a * 0 := by
        rw [ha, hb1, h1, bitBicharacter_eval_ofAdd]
      have h_right : rootSignBit p a *
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) b).toAdd =
            rootSignBit p a * 0 := by
        rw [h_toAdd b, ite_eq_right hb]
      rw [h_left, h_right]
  simp only [h_eval]
  have h_eq : ∀ s : Root n,
      (∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
          rootSignBit p s *
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) t).toAdd) =
        if r0 ≤ s then rootSignBit p s else 0 := by
    intro s
    have h_inner : ∀ t ∈ Finset.univ.filter (fun t => t ≤ s),
        rootSignBit p s *
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) t).toAdd =
          if t = r0 then rootSignBit p s else 0 := by
      intro t _
      rw [h_toAdd t]
      by_cases ht : t = r0
      · simp [ht]
      · simp [ht]
    by_cases hs : r0 ≤ s
    · have h_mem : r0 ∈ Finset.univ.filter (fun t => t ≤ s) := by simp [hs]
      have h_sum : (∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
            if t = r0 then rootSignBit p s else (0 : ZMod 2)) =
          rootSignBit p s := by
        rw [Finset.sum_ite_eq' _ _ (fun _ => rootSignBit p s)]
        simp [h_mem]
      calc (∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
            rootSignBit p s *
              (permute (rootPerm p) (rootSign (Equiv.swap k l)) t).toAdd)
          = ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
              if t = r0 then rootSignBit p s else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            exact h_inner t ht
        _ = rootSignBit p s := h_sum
        _ = if r0 ≤ s then rootSignBit p s else 0 := by rw [ite_eq_left hs]
    · have h_not : ∀ t ∈ Finset.univ.filter (fun t => t ≤ s), t ≠ r0 := by
        intro t ht heq
        rw [heq] at ht
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and] at ht
        exact hs ht
      have h_zero : ∀ t ∈ Finset.univ.filter (fun t => t ≤ s),
          (if t = r0 then rootSignBit p s else (0 : ZMod 2)) = 0 := by
        intro t ht
        rw [ite_eq_right (h_not t ht)]
      calc (∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
            rootSignBit p s *
              (permute (rootPerm p) (rootSign (Equiv.swap k l)) t).toAdd)
          = ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
              if t = r0 then rootSignBit p s else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            exact h_inner t ht
        _ = 0 := Finset.sum_eq_zero h_zero
        _ = if r0 ≤ s then rootSignBit p s else 0 := by rw [ite_eq_right hs]
  calc (∑ s : Root n, ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
          rootSignBit p s *
            (permute (rootPerm p) (rootSign (Equiv.swap k l)) t).toAdd)
      = ∑ s : Root n, if r0 ≤ s then rootSignBit p s else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        exact h_eq s

private theorem lowerSum_delta_perm_swap {n : Nat}
    {i j : Fin n} (hij : j.val = i.val + 1)
    (p : Equiv.Perm (Fin n)) :
    lowerSum bitBicharacter (rootSign (Equiv.swap i j))
        (permute (rootPerm (Equiv.swap i j)) (rootSign p)) =
      ∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0 := by
  classical
  have h_delta : ∀ r : Root n, (rootSign (Equiv.swap i j) r).toAdd =
        if r = mkRoot i j (adjSwap_ne hij) then 1 else 0 := by
    intro r
    exact rootSign_swap_adj_delta hij r
  unfold lowerSum
  have h_eval : ∀ (a b : Root n),
      bitBicharacter.eval (rootSign (Equiv.swap i j) a)
        (permute (rootPerm (Equiv.swap i j)) (rootSign p) b) =
        (if a = mkRoot i j (adjSwap_ne hij) then 1 else (0 : ZMod 2)) *
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ b) := by
    intro a b
    have ha : rootSign (Equiv.swap i j) a =
        Multiplicative.ofAdd
          (if a = mkRoot i j (adjSwap_ne hij) then 1 else 0) := by
      apply congrArg Multiplicative.ofAdd
      exact h_delta a
    have hb : permute (rootPerm (Equiv.swap i j)) (rootSign p) b =
        Multiplicative.ofAdd
          (rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ b)) := rfl
    rw [ha, hb, bitBicharacter_eval_ofAdd]
  simp only [h_eval]
  have h_eq : ∀ s : Root n,
      (∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
          (if s = mkRoot i j (adjSwap_ne hij) then (1 : ZMod 2) else 0) *
            rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t)) =
        if s = mkRoot i j (adjSwap_ne hij) then
          (∑ t ∈ Finset.univ.filter (fun t => t ≤ mkRoot i j (adjSwap_ne hij)),
            rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t)) else 0 := by
    intro s
    by_cases hs : s = mkRoot i j (adjSwap_ne hij)
    · simp [hs]
    · have h_zero : (if s = mkRoot i j (adjSwap_ne hij) then
            (1 : ZMod 2) else 0) = 0 := by simp [hs]
      have h_left_zero : ∀ t ∈ Finset.univ.filter (fun t => t ≤ s),
          (if s = mkRoot i j (adjSwap_ne hij) then (1 : ZMod 2) else 0) *
            rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t) = 0 := by
        intro t _
        rw [h_zero, zero_mul]
      rw [Finset.sum_eq_zero h_left_zero, ite_eq_right hs]
  have h_sum : (∑ s : Root n, ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
        (if s = mkRoot i j (adjSwap_ne hij) then (1 : ZMod 2) else 0) *
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t)) =
      ∑ t ∈ Finset.univ.filter (fun t => t ≤ mkRoot i j (adjSwap_ne hij)),
        rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t) := by
    calc (∑ s : Root n, ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
          (if s = mkRoot i j (adjSwap_ne hij) then (1 : ZMod 2) else 0) *
            rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t))
        = ∑ s : Root n, if s = mkRoot i j (adjSwap_ne hij) then
            (∑ t ∈ Finset.univ.filter (fun t =>
                t ≤ mkRoot i j (adjSwap_ne hij)),
              rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t)) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          exact h_eq s
      _ = ∑ t ∈ Finset.univ.filter (fun t =>
            t ≤ mkRoot i j (adjSwap_ne hij)),
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t) := by
        rw [Finset.sum_ite_eq' Finset.univ (mkRoot i j (adjSwap_ne hij))
          (fun _ => ∑ t ∈ Finset.univ.filter (fun t =>
              t ≤ mkRoot i j (adjSwap_ne hij)),
            rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t))]
        simp
  calc (∑ s : Root n, ∑ t ∈ Finset.univ.filter (fun t => t ≤ s),
        (if s = mkRoot i j (adjSwap_ne hij) then (1 : ZMod 2) else 0) *
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t))
      = ∑ t ∈ Finset.univ.filter (fun t =>
            t ≤ mkRoot i j (adjSwap_ne hij)),
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ t) := h_sum
    _ = ∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
          rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0 := by
        rw [Finset.sum_filter]

private theorem swap_lt_i_iff {n : Nat} {i j : Fin n}
    (hij : j.val = i.val + 1) (a : Fin n) :
    Equiv.swap i j a < i ↔ a < i := by
  classical
  have h_ij : i < j := adjSwap_lt hij
  have h_swap_val : ∀ a : Fin n,
      (Equiv.swap i j a).val = natSwap i.val j.val a.val :=
    swap_adj_apply_val
  have h_nat : ∀ x : Nat, natSwap i.val j.val x < i.val ↔ x < i.val := by
    intro x
    unfold natSwap
    by_cases hx_i : x = i.val
    · rw [ite_eq_left hx_i]
      have hj_not_lt : ¬(j.val < i.val) := by omega
      simp [hx_i, hj_not_lt]
    · by_cases hx_j : x = j.val
      · rw [ite_eq_right hx_i, ite_eq_left hx_j]
        have hx_not_lt : ¬(x < i.val) := by omega
        simp [hx_not_lt]
      · rw [ite_eq_right hx_i, ite_eq_right hx_j]
  have h_fin : ∀ a : Fin n, (Equiv.swap i j a).val < i.val ↔ a.val < i.val := by
    intro a
    have h1 := h_nat a.val
    rw [← h_swap_val a] at h1
    exact h1
  calc Equiv.swap i j a < i ↔ (Equiv.swap i j a).val < i.val :=
        Fin.lt_def
    _ ↔ a.val < i.val := h_fin a
    _ ↔ a < i := Fin.lt_def.symm

private theorem root_le_r0_iff {n : Nat} {i j : Fin n}
    (hij : j.val = i.val + 1) (r : Root n) :
    r ≤ mkRoot i j (adjSwap_ne hij) ↔
      r = mkRoot i j (adjSwap_ne hij) ∨ r.1.1 < i := by
  classical
  have hr0 : mkRoot i j (adjSwap_ne hij) =
      (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
    apply Subtype.ext
    simp [mkRoot, min_eq_left (adjSwap_lt hij).le,
      max_eq_right (adjSwap_lt hij).le]
  have h_le : r ≤ mkRoot i j (adjSwap_ne hij) ↔
      r ≤ (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
    rw [hr0]
  have h_toLex : r ≤ (⟨(i, j), adjSwap_lt hij⟩ : Root n) ↔
      toLex r.1 ≤ toLex ((i, j) : Fin n × Fin n) := Iff.rfl
  have h_lex : toLex r.1 ≤ toLex ((i, j) : Fin n × Fin n) ↔
      r.1.1 < i ∨ (r.1.1 = i ∧ r.1.2 ≤ j) := by
    rw [Prod.Lex.toLex_le_toLex]
  have h_eq : (r.1.1 = i ∧ r.1.2 ≤ j) ↔
      r = mkRoot i j (adjSwap_ne hij) := by
    constructor
    · intro ⟨h1, h2⟩
      have hr_lt : r.1.1 < r.1.2 := r.2
      have h_val : r.1.2.val ≤ j.val := Fin.le_def.mp h2
      have h_lt : i.val < r.1.2.val := by
        rw [← h1]
        exact Fin.lt_def.mp hr_lt
      have h_eq_val : r.1.2.val = j.val := by omega
      have h_eq2 : r.1.2 = j := Fin.ext h_eq_val
      have h_r1 : r.1 = (i, j) := Prod.ext h1 h_eq2
      have hr0_val : (mkRoot i j (adjSwap_ne hij)).1 = (i, j) := by
        simp [hr0]
      have h_r_eq : r.1 = (mkRoot i j (adjSwap_ne hij)).1 := by
        rw [h_r1, hr0_val]
      exact Subtype.ext h_r_eq
    · intro h_eq
      rw [h_eq]
      simp [hr0]
  calc r ≤ mkRoot i j (adjSwap_ne hij) ↔
      r ≤ (⟨(i, j), adjSwap_lt hij⟩ : Root n) := h_le
    _ ↔ toLex r.1 ≤ toLex ((i, j) : Fin n × Fin n) := h_toLex
    _ ↔ r.1.1 < i ∨ (r.1.1 = i ∧ r.1.2 ≤ j) := h_lex
    _ ↔ r.1.1 < i ∨ r = mkRoot i j (adjSwap_ne hij) := by
        rw [h_eq]
    _ ↔ r = mkRoot i j (adjSwap_ne hij) ∨ r.1.1 < i := by
        rw [or_comm]

private def rootLexLt (a b c d : Nat) : Prop :=
  a < c ∨ (a = c ∧ b < d)

private theorem natSwap_root_inversion_iff
    {x y a b c d : Nat} (hy : y = x + 1)
    (hab : a < b) (hcd : c < d) :
    (rootLexLt a b c d ∧
      rootLexLt
        (min (natSwap x y c) (natSwap x y d))
        (max (natSwap x y c) (natSwap x y d))
        (min (natSwap x y a) (natSwap x y b))
        (max (natSwap x y a) (natSwap x y b))) ↔
      (a = c ∧ a < x ∧ b = x ∧ d = y) ∨
        (a = x ∧ c = y ∧ y < b ∧ y < d) := by
  unfold rootLexLt natSwap
  split_ifs at * <;> omega

private theorem rootPerm_swap_adj_inversion_iff {n : Nat}
    {i j : Fin n} (hij : j.val = i.val + 1)
    (r s : Root n) :
    (r < s ∧ rootPerm (Equiv.swap i j) s <
        rootPerm (Equiv.swap i j) r) ↔
      (r.1.1 = s.1.1 ∧ r.1.1 < i ∧
          r.1.2 = i ∧ s.1.2 = j) ∨
        (r.1.1 = i ∧ s.1.1 = j ∧
          j < r.1.2 ∧ j < s.1.2) := by
  have hab : r.1.1.val < r.1.2.val := Fin.lt_def.mp r.2
  have hcd : s.1.1.val < s.1.2.val := Fin.lt_def.mp s.2
  have h_lt : r < s ↔
      rootLexLt r.1.1.val r.1.2.val s.1.1.val s.1.2.val := by
    unfold rootLexLt
    rw [show r < s ↔ toLex r.1 < toLex s.1 from Iff.rfl]
    have h_lex : toLex r.1 < toLex s.1 ↔
        r.1.1 < s.1.1 ∨ (r.1.1 = s.1.1 ∧ r.1.2 < s.1.2) := by
      rw [Prod.Lex.lt_iff]
      simp
    rw [h_lex]
    constructor
    · intro h
      rcases h with h1 | ⟨heq, h2⟩
      · left
        exact Fin.lt_def.mp h1
      · right
        exact ⟨congrArg Fin.val heq, Fin.lt_def.mp h2⟩
    · intro h
      rcases h with h1 | ⟨heq, h2⟩
      · left
        exact Fin.lt_def.mpr h1
      · right
        exact ⟨Fin.ext heq, Fin.lt_def.mpr h2⟩
  have h_swap_min_max : ∀ t : Root n,
      (rootPerm (Equiv.swap i j) t).1.1.val =
        min (natSwap i.val j.val t.1.1.val)
          (natSwap i.val j.val t.1.2.val) ∧
      (rootPerm (Equiv.swap i j) t).1.2.val =
        max (natSwap i.val j.val t.1.1.val)
          (natSwap i.val j.val t.1.2.val) := by
    intro t
    have ha := swap_adj_apply_val (i := i) (j := j) t.1.1
    have hb := swap_adj_apply_val (i := i) (j := j) t.1.2
    have h_perm : rootPerm (Equiv.swap i j) t =
        mkRoot (Equiv.swap i j t.1.1) (Equiv.swap i j t.1.2)
          ((Equiv.swap i j).injective.ne t.2.ne) := rfl
    simp only [h_perm, mkRoot] at *
    have h_min_val :
        (min (Equiv.swap i j t.1.1) (Equiv.swap i j t.1.2)).val =
          min (Equiv.swap i j t.1.1).val
            (Equiv.swap i j t.1.2).val := by
      by_cases h : Equiv.swap i j t.1.1 ≤ Equiv.swap i j t.1.2
      · simp [min_eq_left h, min_eq_left (Fin.le_def.mp h)]
      · have h' : ¬ (Equiv.swap i j t.1.1).val ≤
            (Equiv.swap i j t.1.2).val := by
          intro h_le
          exact h (Fin.le_def.mpr h_le)
        simp [min_eq_right (le_of_not_ge h),
          min_eq_right (le_of_not_ge h')]
    have h_max_val :
        (max (Equiv.swap i j t.1.1) (Equiv.swap i j t.1.2)).val =
          max (Equiv.swap i j t.1.1).val
            (Equiv.swap i j t.1.2).val := by
      by_cases h : Equiv.swap i j t.1.1 ≤ Equiv.swap i j t.1.2
      · simp [max_eq_right h, max_eq_right (Fin.le_def.mp h)]
      · have h' : ¬ (Equiv.swap i j t.1.1).val ≤
            (Equiv.swap i j t.1.2).val := by
          intro h_le
          exact h (Fin.le_def.mpr h_le)
        simp [max_eq_left (le_of_not_ge h),
          max_eq_left (le_of_not_ge h')]
    constructor
    · rw [h_min_val, ha, hb]
    · rw [h_max_val, ha, hb]
  have h_perm_lt :
      rootPerm (Equiv.swap i j) s < rootPerm (Equiv.swap i j) r ↔
        rootLexLt
          (min (natSwap i.val j.val s.1.1.val)
            (natSwap i.val j.val s.1.2.val))
          (max (natSwap i.val j.val s.1.1.val)
            (natSwap i.val j.val s.1.2.val))
          (min (natSwap i.val j.val r.1.1.val)
            (natSwap i.val j.val r.1.2.val))
          (max (natSwap i.val j.val r.1.1.val)
            (natSwap i.val j.val r.1.2.val)) := by
    unfold rootLexLt
    rw [show rootPerm (Equiv.swap i j) s <
        rootPerm (Equiv.swap i j) r ↔
        toLex (rootPerm (Equiv.swap i j) s).1 <
          toLex (rootPerm (Equiv.swap i j) r).1 from Iff.rfl]
    have h_lex : toLex (rootPerm (Equiv.swap i j) s).1 <
        toLex (rootPerm (Equiv.swap i j) r).1 ↔
        (rootPerm (Equiv.swap i j) s).1.1 <
            (rootPerm (Equiv.swap i j) r).1.1 ∨
          ((rootPerm (Equiv.swap i j) s).1.1 =
              (rootPerm (Equiv.swap i j) r).1.1 ∧
            (rootPerm (Equiv.swap i j) s).1.2 <
              (rootPerm (Equiv.swap i j) r).1.2) := by
      rw [Prod.Lex.lt_iff]
      simp
    rw [h_lex]
    have hs := h_swap_min_max s
    have hr := h_swap_min_max r
    simp only [Fin.lt_def, Fin.ext_iff, hs.1, hs.2, hr.1, hr.2]
  calc (r < s ∧ rootPerm (Equiv.swap i j) s <
      rootPerm (Equiv.swap i j) r)
      ↔ (rootLexLt r.1.1.val r.1.2.val s.1.1.val s.1.2.val ∧
          rootLexLt
            (min (natSwap i.val j.val s.1.1.val)
              (natSwap i.val j.val s.1.2.val))
            (max (natSwap i.val j.val s.1.1.val)
              (natSwap i.val j.val s.1.2.val))
            (min (natSwap i.val j.val r.1.1.val)
              (natSwap i.val j.val r.1.2.val))
            (max (natSwap i.val j.val r.1.1.val)
              (natSwap i.val j.val r.1.2.val))) := by
        rw [h_lt, h_perm_lt]
    _ ↔ (r.1.1.val = s.1.1.val ∧ r.1.1.val < i.val ∧
          r.1.2.val = i.val ∧ s.1.2.val = j.val) ∨
        (r.1.1.val = i.val ∧ s.1.1.val = j.val ∧
          j.val < r.1.2.val ∧ j.val < s.1.2.val) := by
        exact natSwap_root_inversion_iff hij hab hcd
    _ ↔ (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
        (r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) := by
        simp only [Fin.ext_iff, Fin.lt_def]

private def rootsAI {n : Nat} (i : Fin n) : Finset (Root n) :=
  Finset.univ.filter fun r => r.1.1 < i ∧ r.1.2 = i

private def rootsIB {n : Nat} (i j : Fin n) : Finset (Root n) :=
  Finset.univ.filter fun r => r.1.1 = i ∧ j < r.1.2

private def rootsJB {n : Nat} (j : Fin n) : Finset (Root n) :=
  Finset.univ.filter fun r => r.1.1 = j ∧ j < r.1.2

private theorem inversionSum_swap_adj_eq_parts
    {n : Nat} {i j : Fin n} (hij : j.val = i.val + 1)
    (p : Equiv.Perm (Fin n))
    (hinv : ∀ r, rootSignBit p (rootPerm (Equiv.swap i j) r) =
      rootSignBit p r) :
    inversionSum bitBicharacter (rootPerm (Equiv.swap i j))
        (rootSign p) =
      (rootsAI i).sum (rootSignBit p) +
        (rootsIB i j).sum (rootSignBit p) := by
  classical
  have h_eval : ∀ r s : Root n,
      bitBicharacter.eval (rootSign p r) (rootSign p s) =
        rootSignBit p r * rootSignBit p s :=
    fun r s => bitBicharacter_eval_rootSign (p := p) r s
  have h_sq : ∀ a : ZMod 2, a * a = a := by
    intro a
    have h := zmod2_eq_zero_or_one a
    rcases h with rfl | rfl
    · simp
    · simp
  have h_two : (2 : ZMod 2) = 0 := by decide
  have h_unfold : inversionSum bitBicharacter
      (rootPerm (Equiv.swap i j)) (rootSign p) =
      ∑ r : Root n, ∑ s ∈ Finset.univ.filter
        (fun s => r < s ∧
          rootPerm (Equiv.swap i j) s <
            rootPerm (Equiv.swap i j) r),
        rootSignBit p r * rootSignBit p s := by
    unfold inversionSum
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    rw [h_eval]
  rw [h_unfold]
  have h_iff : ∀ r s : Root n,
      (r < s ∧ rootPerm (Equiv.swap i j) s <
        rootPerm (Equiv.swap i j) r) ↔
      (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
        (r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) :=
    fun r s => rootPerm_swap_adj_inversion_iff hij r s
  have h_filter_eq : ∀ r : Root n,
      Finset.univ.filter
        (fun (s : Root n) => r < s ∧
          rootPerm (Equiv.swap i j) s <
            rootPerm (Equiv.swap i j) r) =
      Finset.univ.filter
        (fun (s : Root n) =>
          (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
            (r.1.1 = i ∧ s.1.1 = j ∧
              j < r.1.2 ∧ j < s.1.2)) := by
    intro r
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      h_iff r s]
  have h_inner_eq : ∀ r : Root n,
      (∑ s ∈ Finset.univ.filter
        (fun (s : Root n) => r < s ∧
          rootPerm (Equiv.swap i j) s <
            rootPerm (Equiv.swap i j) r),
        rootSignBit p r * rootSignBit p s) =
      (∑ s ∈ Finset.univ.filter
        (fun (s : Root n) =>
          (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
            (r.1.1 = i ∧ s.1.1 = j ∧
              j < r.1.2 ∧ j < s.1.2)),
        rootSignBit p r * rootSignBit p s) := by
    intro r
    rw [h_filter_eq r]
  simp only [h_inner_eq]
  have h_split : ∀ r : Root n,
      Finset.univ.filter
        (fun (s : Root n) =>
          (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
            (r.1.1 = i ∧ s.1.1 = j ∧
              j < r.1.2 ∧ j < s.1.2)) =
      (Finset.univ.filter
        fun (s : Root n) =>
          r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∪
        (Finset.univ.filter
          fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) := by
    intro r
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
  have h_disj : ∀ r : Root n,
      Disjoint
        (Finset.univ.filter
          fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j)
        (Finset.univ.filter
          fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) := by
    intro r
    rw [Finset.disjoint_left]
    intro s hsA hsB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsA hsB
    have h_lt : r.1.1 < i := hsA.2.1
    have h_eq : r.1.1 = i := hsB.1
    rw [h_eq] at h_lt
    exact lt_irrefl _ h_lt
  have h_inner_split : ∀ r : Root n,
      (∑ s ∈ Finset.univ.filter
        (fun (s : Root n) =>
          (r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) ∨
            (r.1.1 = i ∧ s.1.1 = j ∧
              j < r.1.2 ∧ j < s.1.2)),
        rootSignBit p r * rootSignBit p s) =
      (∑ s ∈ Finset.univ.filter
        (fun (s : Root n) =>
          r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
        rootSignBit p r * rootSignBit p s) +
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
          rootSignBit p r * rootSignBit p s) := by
    intro r
    rw [h_split r, Finset.sum_union (h_disj r)]
  simp only [h_inner_split]
  rw [Finset.sum_add_distrib]
  have h_sum_A : (∑ r : Root n,
      ∑ s ∈ Finset.univ.filter
        (fun (s : Root n) =>
          r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
        rootSignBit p r * rootSignBit p s) =
      (rootsAI i).sum (rootSignBit p) := by
    have h_A_zero : ∀ r : Root n, r ∉ rootsAI i →
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
          rootSignBit p r * rootSignBit p s) = 0 := by
      intro r hr
      have h_empty : Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have h_mem : r ∈ rootsAI i := by
          simp [rootsAI, Finset.mem_filter, hs.2.1, hs.2.2.1]
        exact hr h_mem
      rw [h_empty, Finset.sum_empty]
    have h_A_eq : ∀ r : Root n, r ∈ rootsAI i →
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
          rootSignBit p r * rootSignBit p s) =
        rootSignBit p r := by
      intro r hr
      have h_lt : r.1.1 < i := (Finset.mem_filter.mp hr).2.1
      have h_eq : r.1.2 = i := (Finset.mem_filter.mp hr).2.2
      have h_lt_j : r.1.1 < j := lt_trans h_lt (adjSwap_lt hij)
      have h_perm_eq : rootPerm (Equiv.swap i j) r =
          ⟨(r.1.1, j), h_lt_j⟩ := by
        apply Subtype.ext
        simp only [rootPerm_apply, mkRoot]
        have h_swap_a : Equiv.swap i j r.1.1 = r.1.1 := by
          apply Equiv.swap_apply_of_ne_of_ne
          · exact ne_of_lt h_lt
          · exact ne_of_lt h_lt_j
        have h_swap_b : Equiv.swap i j r.1.2 = j := by
          rw [h_eq, Equiv.swap_apply_left]
        rw [h_swap_a, h_swap_b]
        simp [min_eq_left h_lt_j.le, max_eq_right h_lt_j.le]
      have h_filter_single :
          Finset.univ.filter
            (fun (s : Root n) =>
              r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j) =
          {rootPerm (Equiv.swap i j) r} := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          have h_s1 : s.1.1 = r.1.1 := h.1.symm
          have h_s2 : s.1.2 = j := h.2.2.2
          rw [h_perm_eq]
          apply Subtype.ext
          exact Prod.ext h_s1 h_s2
        · intro h
          rw [h, h_perm_eq]
          simp [h_lt, h_eq]
      rw [h_filter_single, Finset.sum_singleton]
      have h_bit_perm : rootSignBit p (rootPerm (Equiv.swap i j) r) =
          rootSignBit p r := hinv r
      calc rootSignBit p r *
          rootSignBit p (rootPerm (Equiv.swap i j) r) =
          rootSignBit p r * rootSignBit p r := by rw [h_bit_perm]
        _ = rootSignBit p r := h_sq _
    have h_outer : ∀ r : Root n,
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
          rootSignBit p r * rootSignBit p s) =
        if r ∈ rootsAI i then rootSignBit p r else 0 := by
      intro r
      by_cases hr : r ∈ rootsAI i
      · rw [h_A_eq r hr, ite_eq_left hr]
      · rw [h_A_zero r hr, ite_eq_right hr]
    calc (∑ r : Root n,
        ∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = s.1.1 ∧ r.1.1 < i ∧ r.1.2 = i ∧ s.1.2 = j),
          rootSignBit p r * rootSignBit p s)
        = ∑ r : Root n,
            if r ∈ rootsAI i then rootSignBit p r else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          exact h_outer r
      _ = ∑ r ∈ Finset.univ.filter (fun r => r ∈ rootsAI i),
            rootSignBit p r := by
          rw [← Finset.sum_filter]
      _ = (rootsAI i).sum (rootSignBit p) := by
          have h_eq : Finset.univ.filter
              (fun r => r ∈ rootsAI i) = rootsAI i := by
            ext r
            simp
          rw [h_eq]
  have h_sum_B : (∑ r : Root n,
      ∑ s ∈ Finset.univ.filter
        (fun (s : Root n) =>
          r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
        rootSignBit p r * rootSignBit p s) =
      (rootsIB i j).sum (rootSignBit p) := by
    have h_B_zero : ∀ r : Root n, r ∉ rootsIB i j →
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
          rootSignBit p r * rootSignBit p s) = 0 := by
      intro r hr
      have h_empty : Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have h_mem : r ∈ rootsIB i j := by
          simp [rootsIB, Finset.mem_filter, hs.1, hs.2.2.1]
        exact hr h_mem
      rw [h_empty, Finset.sum_empty]
    have h_B_eq : ∀ r : Root n, r ∈ rootsIB i j →
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
          rootSignBit p r * rootSignBit p s) =
        rootSignBit p r * (rootsJB j).sum (rootSignBit p) := by
      intro r hr
      have h_eq : Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2) =
          rootsJB j := by
        ext s
        simp only [rootsJB, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact ⟨h.2.1, h.2.2.2⟩
        · intro h
          have h_r1 : r.1.1 = i :=
            (Finset.mem_filter.mp hr).2.1
          have h_r2 : j < r.1.2 :=
            (Finset.mem_filter.mp hr).2.2
          exact ⟨h_r1, h.1, h_r2, h.2⟩
      rw [h_eq, Finset.mul_sum]
    have h_outer_B : ∀ r : Root n,
        (∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
          rootSignBit p r * rootSignBit p s) =
        if r ∈ rootsIB i j then
          rootSignBit p r * (rootsJB j).sum (rootSignBit p) else 0 := by
      intro r
      by_cases hr : r ∈ rootsIB i j
      · rw [h_B_eq r hr, ite_eq_left hr]
      · rw [h_B_zero r hr, ite_eq_right hr]
    have h_JB_eq_IB : (rootsJB j).sum (rootSignBit p) =
        (rootsIB i j).sum (rootSignBit p) := by
      have h_perm_JB_to_IB : ∀ r ∈ rootsJB j,
          rootPerm (Equiv.swap i j) r ∈ rootsIB i j := by
        intro r hr
        have h1 : r.1.1 = j := (Finset.mem_filter.mp hr).2.1
        have h2 : j < r.1.2 := (Finset.mem_filter.mp hr).2.2
        have h_lt_i_j : i < j := adjSwap_lt hij
        have h_i_lt : i < r.1.2 := lt_trans h_lt_i_j h2
        have h_perm_eq : rootPerm (Equiv.swap i j) r =
            ⟨(i, r.1.2), h_i_lt⟩ := by
          apply Subtype.ext
          simp only [rootPerm_apply, mkRoot]
          have h_swap_j : Equiv.swap i j r.1.1 = i := by
            rw [h1, Equiv.swap_apply_right]
          have h_swap_b : Equiv.swap i j r.1.2 = r.1.2 := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact Ne.symm (ne_of_lt h_i_lt)
            · exact Ne.symm (ne_of_lt h2)
          rw [h_swap_j, h_swap_b]
          simp [min_eq_left h_i_lt.le, max_eq_right h_i_lt.le]
        rw [h_perm_eq]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change i = i ∧ j < r.1.2
        exact ⟨rfl, h2⟩
      have h_perm_IB_to_JB : ∀ r ∈ rootsIB i j,
          rootPerm (Equiv.swap i j) r ∈ rootsJB j := by
        intro r hr
        have h1 : r.1.1 = i := (Finset.mem_filter.mp hr).2.1
        have h2 : j < r.1.2 := (Finset.mem_filter.mp hr).2.2
        have h_lt_i_j : i < j := adjSwap_lt hij
        have h_j_lt : j < r.1.2 := h2
        have h_perm_eq : rootPerm (Equiv.swap i j) r =
            ⟨(j, r.1.2), h_j_lt⟩ := by
          apply Subtype.ext
          simp only [rootPerm_apply, mkRoot]
          have h_swap_i : Equiv.swap i j r.1.1 = j := by
            rw [h1, Equiv.swap_apply_left]
          have h_swap_b : Equiv.swap i j r.1.2 = r.1.2 := by
            apply Equiv.swap_apply_of_ne_of_ne
            · exact Ne.symm (ne_of_lt (lt_trans h_lt_i_j h2))
            · exact Ne.symm (ne_of_lt h2)
          rw [h_swap_i, h_swap_b]
          simp [min_eq_left h_j_lt.le, max_eq_right h_j_lt.le]
        rw [h_perm_eq]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change j = j ∧ j < r.1.2
        exact ⟨rfl, h_j_lt⟩
      have h_image : rootsIB i j =
          (rootsJB j).image (rootPerm (Equiv.swap i j)) := by
        ext r
        simp only [Finset.mem_image]
        constructor
        · intro hr
          have h_perm : rootPerm (Equiv.swap i j)
              (rootPerm (Equiv.swap i j) r) = r := by
            have h_sq : rootPerm (Equiv.swap i j) *
                rootPerm (Equiv.swap i j) = 1 := by
              rw [← rootPerm_mul, Equiv.swap_mul_self, rootPerm_one]
            have h1 := congrArg (fun σ => σ r) h_sq
            simp only [Equiv.Perm.one_apply] at h1
            exact h1
          exact ⟨rootPerm (Equiv.swap i j) r,
            h_perm_IB_to_JB r hr, h_perm⟩
        · intro h
          rcases h with ⟨s, hs, rfl⟩
          exact h_perm_JB_to_IB s hs
      have h_sum_perm : (rootsJB j).sum
          (fun s => rootSignBit p (rootPerm (Equiv.swap i j) s)) =
          (rootsJB j).sum (rootSignBit p) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hinv s
      calc (rootsJB j).sum (rootSignBit p) =
          (rootsJB j).sum
            (fun s => rootSignBit p (rootPerm (Equiv.swap i j) s)) := by
            rw [← h_sum_perm]
        _ = ((rootsJB j).image (rootPerm (Equiv.swap i j))).sum
              (rootSignBit p) := by
            rw [Finset.sum_image]
            intro x hx y hy h_eq
            exact (rootPerm (Equiv.swap i j)).injective h_eq
        _ = (rootsIB i j).sum (rootSignBit p) := by
            rw [← h_image]
    calc (∑ r : Root n,
        ∑ s ∈ Finset.univ.filter
          (fun (s : Root n) =>
            r.1.1 = i ∧ s.1.1 = j ∧ j < r.1.2 ∧ j < s.1.2),
          rootSignBit p r * rootSignBit p s)
        = ∑ r : Root n,
            if r ∈ rootsIB i j then
              rootSignBit p r * (rootsJB j).sum (rootSignBit p) else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          exact h_outer_B r
      _ = ∑ r ∈ Finset.univ.filter (fun r => r ∈ rootsIB i j),
            rootSignBit p r * (rootsJB j).sum (rootSignBit p) := by
          rw [← Finset.sum_filter]
      _ = (∑ r ∈ rootsIB i j, rootSignBit p r) *
            (rootsJB j).sum (rootSignBit p) := by
          have h_eq : Finset.univ.filter
              (fun r => r ∈ rootsIB i j) = rootsIB i j := by
            ext r
            simp
          rw [h_eq, Finset.sum_mul]
      _ = (rootsIB i j).sum (rootSignBit p) *
            (rootsIB i j).sum (rootSignBit p) := by
          rw [h_JB_eq_IB]
      _ = (rootsIB i j).sum (rootSignBit p) := by
          rw [h_sq]
  rw [h_sum_A, h_sum_B]

private def rootIncidence {n : Nat} (v : Root n → ZMod 2)
    (i : Fin n) (b : Fin n) : ZMod 2 :=
  if h : b = i then 0 else v (mkRoot i b (Ne.symm h))

private theorem rootIncidence_eq_indicator {n : Nat}
    (p : Equiv.Perm (Fin n)) (i b : Fin n) :
    rootIncidence (rootSignBit p) i b =
      (if b < i then (1 : ZMod 2) else 0) +
        if (p⁻¹ b < p⁻¹ i) then 1 else 0 := by
  classical
  unfold rootIncidence
  by_cases hb_eq : b = i
  · simp [hb_eq]
  · have hb_ne : b ≠ i := hb_eq
    have hi_ne : i ≠ b := Ne.symm hb_ne
    rcases lt_or_gt_of_ne hb_ne with hb_lt | hi_lt
    · have h_mk : mkRoot i b hi_ne = ⟨(b, i), hb_lt⟩ :=
        mkRoot_of_gt hb_lt
      have h_bit : rootSignBit p (mkRoot i b hi_ne) =
          if p⁻¹ b < p⁻¹ i then (0 : ZMod 2) else 1 := by
        unfold rootSignBit
        simp [h_mk]
      rw [dite_eq_right hb_eq, h_bit, ite_eq_left hb_lt]
      by_cases hp : p⁻¹ b < p⁻¹ i
      · simp only [hp, ite_true]
        have h_add : (1 : ZMod 2) + 1 = 0 := by decide
        simp only [h_add]
      · simp only [hp, ite_false, add_zero]
    · have h_mk : mkRoot i b hi_ne = ⟨(i, b), hi_lt⟩ :=
        mkRoot_of_lt hi_lt
      have h_bit : rootSignBit p (mkRoot i b hi_ne) =
          if p⁻¹ i < p⁻¹ b then (0 : ZMod 2) else 1 := by
        unfold rootSignBit
        simp [h_mk]
      rw [dite_eq_right hb_eq, h_bit]
      have hb_lt_false : ¬b < i := not_lt.mpr hi_lt.le
      rw [ite_eq_right hb_lt_false]
      have h_ne : p⁻¹ b ≠ p⁻¹ i :=
        p⁻¹.injective.ne hb_ne
      by_cases hp : p⁻¹ b < p⁻¹ i
      · have h_not : ¬p⁻¹ i < p⁻¹ b := not_lt.mpr hp.le
        simp only [hp, h_not, ite_true, ite_false, zero_add]
      · have hp_gt : p⁻¹ i < p⁻¹ b := by
          rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
          · exfalso; exact hp h_lt
          · exact h_gt
        simp only [hp, hp_gt, ite_true, ite_false, add_zero]

private theorem sum_indicator_lt_eq_val {n : Nat} (i : Fin n) :
    (∑ b : Fin n, if b < i then (1 : ZMod 2) else 0) =
      (i.val : ZMod 2) := by
  classical
  have h_eq : (∑ b : Fin n, if b < i then (1 : ZMod 2) else 0) =
      ((Finset.univ.filter (fun b : Fin n => b < i)).card : ZMod 2) := by
    have h1 : (∑ b : Fin n, if b < i then (1 : ZMod 2) else 0) =
        ∑ b ∈ Finset.univ.filter (fun b => b < i), (1 : ZMod 2) := by
      rw [← Finset.sum_filter]
    rw [h1]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b => b < i), (1 : ZMod 2) =
        ((Finset.univ.filter (fun b => b < i)).card : ZMod 2) := by
      have h_card : ∀ s : Finset (Fin n), ∑ _b ∈ s, (1 : ZMod 2) =
          (s.card : ZMod 2) := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, ih, Finset.card_insert_of_notMem ha,
            Nat.cast_add]
          ring
      exact h_card _
    exact h2
  rw [h_eq]
  have h_card : (Finset.univ.filter (fun b : Fin n => b < i)).card =
      i.val := by
    classical
    have h_image : (Finset.univ : Finset (Fin n)).image Fin.val =
        Finset.range n := by
      ext k
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨b, _, rfl⟩
        exact b.isLt
      · intro hk
        exact ⟨⟨k, hk⟩, rfl⟩
    have h_filter_image :
        (Finset.univ.filter (fun b : Fin n => b < i)).image Fin.val =
          Finset.range i.val := by
      ext k
      simp only [Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨b, hb_lt, rfl⟩
        have hv : b.val < i.val := Fin.lt_def.mp hb_lt
        exact hv
      · intro hk
        have hk_n : k < n := by omega
        have hb_lt : (⟨k, hk_n⟩ : Fin n) < i := by
          exact Fin.lt_def.mpr hk
        exact ⟨⟨k, hk_n⟩, hb_lt, rfl⟩
    have h_card_image :
        ((Finset.univ.filter (fun b : Fin n => b < i)).image Fin.val).card =
          (Finset.range i.val).card := by
      rw [h_filter_image]
    have h_inj : Set.InjOn Fin.val
        (Finset.univ.filter (fun b : Fin n => b < i) : Set (Fin n)) := by
      intro a ha b hb hab
      exact Fin.ext hab
    have h_card_eq :
        ((Finset.univ.filter (fun b : Fin n => b < i)).image Fin.val).card =
          (Finset.univ.filter (fun b : Fin n => b < i)).card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_range_card : (Finset.range i.val).card = i.val := by
      simp
    calc (Finset.univ.filter (fun b : Fin n => b < i)).card
        = ((Finset.univ.filter (fun b : Fin n => b < i)).image Fin.val).card := by
          rw [h_card_eq]
      _ = (Finset.range i.val).card := by rw [h_filter_image]
      _ = i.val := by simp
  rw [h_card]

private theorem sum_indicator_pinv_eq_val {n : Nat}
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ b : Fin n, if p⁻¹ b < p⁻¹ i then (1 : ZMod 2) else 0) =
      ((p⁻¹ i).val : ZMod 2) := by
  classical
  have h_reindex :
      (∑ b : Fin n, if p⁻¹ b < p⁻¹ i then (1 : ZMod 2) else 0) =
        ∑ c : Fin n, if c < p⁻¹ i then (1 : ZMod 2) else 0 := by
    calc (∑ b : Fin n, if p⁻¹ b < p⁻¹ i then (1 : ZMod 2) else 0)
        = ∑ b : Fin n, (fun c => if c < p⁻¹ i then (1 : ZMod 2) else 0)
            (p.symm b) := rfl
      _ = ∑ c : Fin n, if c < p⁻¹ i then (1 : ZMod 2) else 0 :=
          Equiv.sum_comp p.symm (fun c => if c < p⁻¹ i then 1 else 0)
  rw [h_reindex]
  exact sum_indicator_lt_eq_val (p⁻¹ i)

private theorem sum_rootIncidence_eq_val {n : Nat}
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (∑ b : Fin n, rootIncidence (rootSignBit p) i b) =
      ((i.val : ZMod 2) + ((p⁻¹ i).val : ZMod 2)) := by
  classical
  have h_eq : ∀ b : Fin n,
      rootIncidence (rootSignBit p) i b =
        (if b < i then (1 : ZMod 2) else 0) +
          if p⁻¹ b < p⁻¹ i then 1 else 0 :=
    fun b => rootIncidence_eq_indicator p i b
  calc (∑ b : Fin n, rootIncidence (rootSignBit p) i b)
      = ∑ b : Fin n,
          ((if b < i then (1 : ZMod 2) else 0) +
            if p⁻¹ b < p⁻¹ i then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        exact h_eq b
    _ = (∑ b : Fin n, if b < i then (1 : ZMod 2) else 0) +
        (∑ b : Fin n, if p⁻¹ b < p⁻¹ i then (1 : ZMod 2) else 0) := by
        rw [Finset.sum_add_distrib]
    _ = (i.val : ZMod 2) + ((p⁻¹ i).val : ZMod 2) := by
        rw [sum_indicator_lt_eq_val, sum_indicator_pinv_eq_val]

private theorem sum_rootIncidence_split {n : Nat} {i j : Fin n}
    (hij : j.val = i.val + 1) (v : Root n → ZMod 2) :
    (∑ b : Fin n, rootIncidence v i b) =
      (rootsAI i).sum v + v (mkRoot i j (adjSwap_ne hij)) +
        (rootsIB i j).sum v := by
  classical
  have h_part : (Finset.univ : Finset (Fin n)) =
      Finset.univ.filter (fun b => b < i) ∪ {i} ∪ {j} ∪
        Finset.univ.filter (fun b => j < b) := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff, or_assoc]
    constructor
    · intro _
      have hb : b.val < i.val ∨ b.val = i.val ∨ b.val = j.val ∨
          j.val < b.val := by omega
      exact hb
    · intro _; trivial
  have h_disj1 : Disjoint
      (Finset.univ.filter (fun b : Fin n => b < i)) {i} := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hb1 hb2
    rw [hb2] at hb1
    exact lt_irrefl _ hb1
  have h_disj2 : Disjoint
      (Finset.univ.filter (fun b : Fin n => b < i) ∪ {i}) {j} := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    simp only [Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] at hb1 hb2
    rw [hb2] at hb1
    have hj : j.val = i.val + 1 := hij
    have : j.val < i.val ∨ j.val = i.val := by
      rcases hb1 with hb_lt | hb_eq
      · exact Or.inl (Fin.lt_def.mp hb_lt)
      · exact Or.inr (congrArg Fin.val hb_eq)
    omega
  have h_disj3 : Disjoint
      (Finset.univ.filter (fun b : Fin n => b < i) ∪ {i} ∪ {j})
      (Finset.univ.filter (fun b : Fin n => j < b)) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    simp only [Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] at hb1 hb2
    have hj : j.val = i.val + 1 := hij
    have hj_lt : j.val < b.val := Fin.lt_def.mp hb2
    rcases hb1 with hb1' | hb_eq2
    · rcases hb1' with hb_lt | hb_eq
      · have : b.val < j.val := by
          have : b.val < i.val := Fin.lt_def.mp hb_lt
          omega
        omega
      · have : b.val = i.val := congrArg Fin.val hb_eq
        omega
    · have : b.val = j.val := congrArg Fin.val hb_eq2
      omega
  have h_sum : (∑ b : Fin n, rootIncidence v i b) =
      (∑ b ∈ Finset.univ.filter (fun b => b < i), rootIncidence v i b) +
        (∑ b ∈ ({i} : Finset (Fin n)), rootIncidence v i b) +
        (∑ b ∈ ({j} : Finset (Fin n)), rootIncidence v i b) +
        (∑ b ∈ Finset.univ.filter (fun b => j < b), rootIncidence v i b) := by
    calc (∑ b : Fin n, rootIncidence v i b)
        = ∑ b ∈ Finset.univ, rootIncidence v i b := rfl
      _ = ∑ b ∈ Finset.univ.filter (fun b => b < i) ∪ {i} ∪ {j} ∪
            Finset.univ.filter (fun b => j < b), rootIncidence v i b := by
          rw [← h_part]
      _ = (∑ b ∈ Finset.univ.filter (fun b => b < i), rootIncidence v i b) +
            (∑ b ∈ {i}, rootIncidence v i b) +
            (∑ b ∈ {j}, rootIncidence v i b) +
            (∑ b ∈ Finset.univ.filter (fun b => j < b), rootIncidence v i b) := by
          rw [Finset.sum_union h_disj3, Finset.sum_union h_disj2,
            Finset.sum_union h_disj1]
  have h_i : (∑ b ∈ ({i} : Finset (Fin n)), rootIncidence v i b) = 0 := by
    simp [rootIncidence]
  have h_j : (∑ b ∈ ({j} : Finset (Fin n)), rootIncidence v i b) =
      v (mkRoot i j (adjSwap_ne hij)) := by
    have hj_ne : j ≠ i := Ne.symm (adjSwap_ne hij)
    have hi_ne : i ≠ j := adjSwap_ne hij
    have h_eq : rootIncidence v i j = v (mkRoot i j hi_ne) := by
      unfold rootIncidence
      rw [dite_eq_right hj_ne]
    simp [h_eq]
  have h_ai : (∑ b ∈ Finset.univ.filter (fun b : Fin n => b < i),
      rootIncidence v i b) = (rootsAI i).sum v := by
    classical
    by_cases hn : n < 2
    · have h_filter_empty :
          (Finset.univ.filter (fun b : Fin n => b < i)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have : b.val < i.val := Fin.lt_def.mp hb
        have : i.val < n := i.isLt
        omega
      have h_roots_empty : rootsAI i = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        simp only [rootsAI, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        have : r.1.1.val < i.val := Fin.lt_def.mp hr.1
        have : i.val < n := i.isLt
        omega
      rw [h_filter_empty, h_roots_empty]
      simp
    · have hn2 : 2 ≤ n := by omega
      let defaultRoot : Root n :=
        ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
          apply Fin.lt_def.mpr
          simp⟩
      let F : Fin n → Root n := fun b =>
        if h : b < i then mkRoot b i (ne_of_lt h) else defaultRoot
      have h_eq : ∀ b ∈ Finset.univ.filter (fun b : Fin n => b < i),
          rootIncidence v i b = v (F b) := by
        intro b hb
        have hb_lt : b < i := (Finset.mem_filter.mp hb).2
        have hb_ne : b ≠ i := ne_of_lt hb_lt
        have hi_ne : i ≠ b := Ne.symm hb_ne
        have h_mk : mkRoot i b hi_ne = mkRoot b i hb_ne := by
          apply Subtype.ext
          simp [mkRoot, min_comm, max_comm]
        have hF : F b = mkRoot b i hb_ne := by
          unfold F
          rw [dite_eq_left hb_lt]
        unfold rootIncidence
        rw [dite_eq_right hb_ne, h_mk, hF]
      calc (∑ b ∈ Finset.univ.filter (fun b : Fin n => b < i),
            rootIncidence v i b)
          = ∑ b ∈ Finset.univ.filter (fun b : Fin n => b < i), v (F b) := by
              apply Finset.sum_congr rfl
              intro b hb
              exact h_eq b hb
        _ = (rootsAI i).sum v := by
            have h_image :
                (Finset.univ.filter (fun b : Fin n => b < i)).image F =
                  rootsAI i := by
              ext r
              simp only [Finset.mem_image, Finset.mem_filter,
                Finset.mem_univ, true_and, rootsAI, Finset.mem_filter]
              constructor
              · rintro ⟨b, hb_lt, hr⟩
                have hF : F b = mkRoot b i (ne_of_lt hb_lt) := by
                  unfold F
                  rw [dite_eq_left hb_lt]
                have hr_eq : r = mkRoot b i (ne_of_lt hb_lt) := by
                  calc r = F b := hr.symm
                    _ = mkRoot b i (ne_of_lt hb_lt) := hF
                have hr_lt : r.1.1 < i := by
                  rw [hr_eq, mkRoot_of_lt hb_lt]
                  exact hb_lt
                have hr_eq2 : r.1.2 = i := by
                  rw [hr_eq, mkRoot_of_lt hb_lt]
                exact ⟨hr_lt, hr_eq2⟩
              · rintro ⟨hb_lt, hb_eq⟩
                refine ⟨r.1.1, hb_lt, ?_⟩
                have h_mk : mkRoot r.1.1 i (ne_of_lt hb_lt) = r := by
                  rw [mkRoot_of_lt hb_lt]
                  apply Subtype.ext
                  exact Prod.ext rfl hb_eq.symm
                have hF : F r.1.1 = mkRoot r.1.1 i (ne_of_lt hb_lt) := by
                  unfold F
                  rw [dite_eq_left hb_lt]
                exact hF.trans h_mk
            have h_inj : Set.InjOn F
                (Finset.univ.filter (fun b : Fin n => b < i) : Set (Fin n)) := by
              intro a ha b hb hab
              have ha_lt : a < i := (Finset.mem_filter.mp ha).2
              have hb_lt : b < i := (Finset.mem_filter.mp hb).2
              have ha_mk : F a = mkRoot a i (ne_of_lt ha_lt) := by
                unfold F; rw [dite_eq_left ha_lt]
              have hb_mk : F b = mkRoot b i (ne_of_lt hb_lt) := by
                unfold F; rw [dite_eq_left hb_lt]
              rw [ha_mk, hb_mk] at hab
              have ha_eq :
                  (mkRoot a i (ne_of_lt ha_lt)).1 = (a, i) := by
                simp [mkRoot, min_eq_left ha_lt.le, max_eq_right ha_lt.le]
              have hb_eq :
                  (mkRoot b i (ne_of_lt hb_lt)).1 = (b, i) := by
                simp [mkRoot, min_eq_left hb_lt.le, max_eq_right hb_lt.le]
              have h1 : (a, i) = (b, i) := by
                calc (a, i) = (mkRoot a i (ne_of_lt ha_lt)).1 := ha_eq.symm
                  _ = (mkRoot b i (ne_of_lt hb_lt)).1 := by rw [hab]
                  _ = (b, i) := hb_eq
              exact (Prod.ext_iff.mp h1).1
            rw [← h_image, Finset.sum_image h_inj]
  have h_ib : (∑ b ∈ Finset.univ.filter (fun b : Fin n => j < b),
      rootIncidence v i b) = (rootsIB i j).sum v := by
    classical
    by_cases hn : n < 2
    · have h_filter_empty :
          (Finset.univ.filter (fun b : Fin n => j < b)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have : j.val < b.val := Fin.lt_def.mp hb
        have : b.val < n := b.isLt
        omega
      have h_roots_empty : rootsIB i j = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        simp only [rootsIB, Finset.mem_filter, Finset.mem_univ, true_and] at hr
        have : j.val < r.1.2.val := Fin.lt_def.mp hr.2
        have : r.1.2.val < n := r.1.2.isLt
        omega
      rw [h_filter_empty, h_roots_empty, Finset.sum_empty, Finset.sum_empty]
    · have hn2 : 2 ≤ n := by omega
      let defaultRoot : Root n :=
        ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by
          apply Fin.lt_def.mpr
          simp⟩
      let G : Fin n → Root n := fun b =>
        if h : j < b then
          mkRoot i b (ne_of_lt (lt_trans (adjSwap_lt hij) h))
        else defaultRoot
      have h_eq : ∀ b ∈ Finset.univ.filter (fun b : Fin n => j < b),
          rootIncidence v i b = v (G b) := by
        intro b hb
        have hb_lt : j < b := (Finset.mem_filter.mp hb).2
        have hi_lt : i < b := lt_trans (adjSwap_lt hij) hb_lt
        have hb_ne : b ≠ i := Ne.symm (ne_of_lt hi_lt)
        have hi_ne : i ≠ b := ne_of_lt hi_lt
        have hG : G b = mkRoot i b hi_ne := by
          unfold G
          rw [dite_eq_left hb_lt]
        unfold rootIncidence
        rw [dite_eq_right hb_ne, hG]
      calc (∑ b ∈ Finset.univ.filter (fun b : Fin n => j < b),
            rootIncidence v i b)
          = ∑ b ∈ Finset.univ.filter (fun b : Fin n => j < b), v (G b) := by
              apply Finset.sum_congr rfl
              intro b hb
              exact h_eq b hb
        _ = (rootsIB i j).sum v := by
            have h_image :
                (Finset.univ.filter (fun b : Fin n => j < b)).image G =
                  rootsIB i j := by
              ext r
              simp only [Finset.mem_image, Finset.mem_filter,
                Finset.mem_univ, true_and, rootsIB, Finset.mem_filter]
              constructor
              · rintro ⟨b, hb_lt, rfl⟩
                have hi_lt : i < b := lt_trans (adjSwap_lt hij) hb_lt
                have hi_ne : i ≠ b := ne_of_lt hi_lt
                have hG : G b = mkRoot i b hi_ne := by
                  unfold G
                  rw [dite_eq_left hb_lt]
                rw [hG, mkRoot_of_lt hi_lt]
                exact ⟨rfl, hb_lt⟩
              · rintro ⟨hr_eq, hb_lt⟩
                refine ⟨r.1.2, hb_lt, ?_⟩
                have hi_lt : i < r.1.2 := lt_trans (adjSwap_lt hij) hb_lt
                have hi_ne : i ≠ r.1.2 := ne_of_lt hi_lt
                have h_mk : mkRoot i r.1.2 hi_ne = r := by
                  rcases r with ⟨⟨a, b⟩, hab⟩
                  subst hr_eq
                  apply Subtype.ext
                  simp [mkRoot_of_lt hi_lt]
                have hG : G r.1.2 = mkRoot i r.1.2 hi_ne := by
                  unfold G
                  rw [dite_eq_left hb_lt]
                rw [hG, h_mk]
            have h_inj : Set.InjOn G
                (Finset.univ.filter (fun b : Fin n => j < b) : Set (Fin n)) := by
              intro a ha b hb hab
              have ha_lt : j < a := (Finset.mem_filter.mp ha).2
              have hb_lt : j < b := (Finset.mem_filter.mp hb).2
              have ha_lt_i : i < a := lt_trans (adjSwap_lt hij) ha_lt
              have hb_lt_i : i < b := lt_trans (adjSwap_lt hij) hb_lt
              have ha_ne : i ≠ a := ne_of_lt ha_lt_i
              have hb_ne : i ≠ b := ne_of_lt hb_lt_i
              have ha_mk : G a = mkRoot i a ha_ne := by
                unfold G; rw [dite_eq_left ha_lt]
              have hb_mk : G b = mkRoot i b hb_ne := by
                unfold G; rw [dite_eq_left hb_lt]
              rw [ha_mk, hb_mk] at hab
              have ha_eq : (mkRoot i a ha_ne).1 = (i, a) := by
                simp [mkRoot, min_eq_left ha_lt_i.le, max_eq_right ha_lt_i.le]
              have hb_eq : (mkRoot i b hb_ne).1 = (i, b) := by
                simp [mkRoot, min_eq_left hb_lt_i.le, max_eq_right hb_lt_i.le]
              have h1 : (i, a) = (i, b) := by
                calc (i, a) = (mkRoot i a ha_ne).1 := ha_eq.symm
                  _ = (mkRoot i b hb_ne).1 := by rw [hab]
                  _ = (i, b) := hb_eq
              exact (Prod.ext_iff.mp h1).2
            rw [← h_image, Finset.sum_image h_inj]
  calc (∑ b : Fin n, rootIncidence v i b)
      = (∑ b ∈ Finset.univ.filter (fun b => b < i), rootIncidence v i b) +
          (∑ b ∈ ({i} : Finset (Fin n)), rootIncidence v i b) +
          (∑ b ∈ ({j} : Finset (Fin n)), rootIncidence v i b) +
          (∑ b ∈ Finset.univ.filter (fun b => j < b), rootIncidence v i b) :=
        h_sum
    _ = (rootsAI i).sum v + 0 + v (mkRoot i j (adjSwap_ne hij)) +
          (rootsIB i j).sum v := by
        rw [h_ai, h_i, h_j, h_ib]
    _ = (rootsAI i).sum v + v (mkRoot i j (adjSwap_ne hij)) +
          (rootsIB i j).sum v := by ring

theorem schurCocycle_pos_overlap {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_k_i : p k = i) (hp_l_j : p l = j) :
    schurCocycle p (Equiv.swap k l) +
        schurCocycle (Equiv.swap i j) p =
      parityBit p + ((i.val + k.val : Nat) : ZMod 2) := by
  classical
  have h_par_kl : parityBit (Equiv.swap k l : Equiv.Perm (Fin n)) = 1 :=
    parityBit_swap_adj hkl
  have h_par_ij : parityBit (Equiv.swap i j : Equiv.Perm (Fin n)) = 1 :=
    parityBit_swap_adj hij
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h_schur : schurCocycle p (Equiv.swap k l) +
      schurCocycle (Equiv.swap i j) p =
      rootCocycle0 p (Equiv.swap k l) +
        rootCocycle0 (Equiv.swap i j) p := by
    calc schurCocycle p (Equiv.swap k l) + schurCocycle (Equiv.swap i j) p
        = rootCocycle0 p (Equiv.swap k l) + parityBit p * parityBit (Equiv.swap k l) +
          (rootCocycle0 (Equiv.swap i j) p + parityBit (Equiv.swap i j) * parityBit p) := by
            simp [schurCocycle]
      _ = rootCocycle0 p (Equiv.swap k l) + parityBit p * 1 +
          (rootCocycle0 (Equiv.swap i j) p + 1 * parityBit p) := by
            rw [h_par_kl, h_par_ij]
      _ = rootCocycle0 p (Equiv.swap k l) + rootCocycle0 (Equiv.swap i j) p +
          2 * parityBit p := by ring
      _ = rootCocycle0 p (Equiv.swap k l) + rootCocycle0 (Equiv.swap i j) p := by
            rw [h2, zero_mul, add_zero]
  rw [h_schur]
  have h_par_eq : parityBit p = ∑ r : Root n, rootSignBit p r :=
    parityBit_eq_sum_rootSignBit p
  have h_left : rootCocycle0 p (Equiv.swap k l) =
      ∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
        rootSignBit p r else 0 := by
    have h1 : rootCocycle0 p (Equiv.swap k l) =
        lowerSum bitBicharacter (rootSign p)
          (permute (rootPerm p) (rootSign (Equiv.swap k l))) +
          inversionSum bitBicharacter (rootPerm p)
            (rootSign (Equiv.swap k l)) := by
      -- unfold rootCocycle0 and monomialAddCocycle
      change monomialAddCocycle bitBicharacter (rootMonomial n p)
          (rootMonomial n (Equiv.swap k l)) = _
      rfl
    have h2 : inversionSum bitBicharacter (rootPerm p)
          (rootSign (Equiv.swap k l)) = 0 :=
      inversionSum_rootPerm_swap_zero p hkl
    have h3 : lowerSum bitBicharacter (rootSign p)
          (permute (rootPerm p) (rootSign (Equiv.swap k l))) =
        ∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
          rootSignBit p r else 0 :=
      lowerSum_rootSign_perm_swap hij hkl p hp_k_i hp_l_j
    calc rootCocycle0 p (Equiv.swap k l) = _ := h1
      _ = (∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
            rootSignBit p r else 0) + 0 := by rw [h3, h2]
      _ = ∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
            rootSignBit p r else 0 := by rw [add_zero]
  have h_right_lower : lowerSum bitBicharacter
        (rootSign (Equiv.swap i j))
        (permute (rootPerm (Equiv.swap i j)) (rootSign p)) =
      ∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0 :=
    lowerSum_delta_perm_swap hij p
  have h_right_eq : rootCocycle0 (Equiv.swap i j) p =
      (∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0) +
        inversionSum bitBicharacter (rootPerm (Equiv.swap i j))
          (rootSign p) := by
    have h1 : rootCocycle0 (Equiv.swap i j) p =
        lowerSum bitBicharacter (rootSign (Equiv.swap i j))
          (permute (rootPerm (Equiv.swap i j)) (rootSign p)) +
          inversionSum bitBicharacter (rootPerm (Equiv.swap i j))
            (rootSign p) := by
      change monomialAddCocycle bitBicharacter
          (rootMonomial n (Equiv.swap i j)) (rootMonomial n p) = _
      rfl
    rw [h1, h_right_lower]
  have h_σ_inv : (rootPerm (Equiv.swap i j) : Equiv.Perm (Root n))⁻¹ =
      rootPerm (Equiv.swap i j) := by
    have h1 : (Equiv.swap i j : Equiv.Perm (Fin n)) *
        Equiv.swap i j = 1 := Equiv.swap_mul_self i j
    have h2 : rootPerm (Equiv.swap i j) * rootPerm (Equiv.swap i j) = 1 := by
      rw [← rootPerm_mul, h1, rootPerm_one]
    exact inv_eq_of_mul_eq_one_right h2
  have h_sum_le_eq : (∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0) =
      ∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p r else 0 := by
    classical
    let σ : Equiv.Perm (Root n) := rootPerm (Equiv.swap i j)
    let r0 : Root n := mkRoot i j (adjSwap_ne hij)
    have hσ_inv : σ⁻¹ = σ := h_σ_inv
    have hσ_symm : σ.symm = σ := by
      calc σ.symm = σ⁻¹ := rfl
        _ = σ := hσ_inv
    have hσ_fixed : σ r0 = r0 := rootPerm_swap_adj_fixed hij
    have h_first_lt : ∀ r : Root n, (σ r).1.1 < i ↔ r.1.1 < i := by
      intro r
      have hr : r = r0 ∨ r ≠ r0 := em (r = r0)
      rcases hr with rfl | hr
      · simp [hσ_fixed]
      · have ha_lt_b : r.1.1 < r.1.2 := r.2
        have h_not_pair : ¬(r.1.1 = i ∧ r.1.2 = j) := by
          intro ⟨h1, h2⟩
          apply hr
          have hr0_eq : r0 = (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
            apply Subtype.ext
            simp [r0, mkRoot, min_eq_left (adjSwap_lt hij).le,
              max_eq_right (adjSwap_lt hij).le]
          apply Subtype.ext
          rw [hr0_eq]
          exact Prod.ext h1 h2
        have h_preserve : Equiv.swap i j r.1.1 < Equiv.swap i j r.1.2 :=
          swap_adj_preserve hij ha_lt_b h_not_pair
        have h_mk : σ r =
            (⟨(Equiv.swap i j r.1.1, Equiv.swap i j r.1.2),
              h_preserve⟩ : Root n) := by
          apply Subtype.ext
          simp only [σ, rootPerm_apply]
          rw [mkRoot_of_lt h_preserve]
        have h_first : (σ r).1.1 = Equiv.swap i j r.1.1 := by
          rw [h_mk]
        rw [h_first]
        exact swap_lt_i_iff hij r.1.1
    have h_le_iff : ∀ r : Root n, r ≤ r0 ↔ σ r ≤ r0 := by
      intro r
      rw [root_le_r0_iff hij, root_le_r0_iff hij]
      constructor
      · intro h
        rcases h with rfl | h_lt
        · exact Or.inl hσ_fixed
        · right
          exact (h_first_lt r).mpr h_lt
      · intro h
        rcases h with h_eq | h_lt
        · left
          have h_inj : Function.Injective σ := σ.injective
          have : r = r0 := by
            have h1 : σ r = σ r0 := by rw [h_eq, hσ_fixed]
            exact h_inj h1
          exact this
        · right
          exact (h_first_lt r).mp h_lt
    have h_le_iff_symm : ∀ r : Root n, r ≤ r0 ↔ σ.symm r ≤ r0 := by
      intro r
      rw [hσ_symm]
      exact h_le_iff r
    have h_eq_fun : ∀ r : Root n,
        (if r ≤ r0 then rootSignBit p (σ.symm r) else (0 : ZMod 2)) =
          (if σ.symm r ≤ r0 then rootSignBit p (σ.symm r) else 0) := by
      intro r
      by_cases h : r ≤ r0
      · have h2 : σ.symm r ≤ r0 := (h_le_iff_symm r).mp h
        rw [ite_eq_left h, ite_eq_left h2]
      · have h2 : ¬σ.symm r ≤ r0 := fun h2 => h ((h_le_iff_symm r).mpr h2)
        rw [ite_eq_right h, ite_eq_right h2]
    have h_rw_inv : (∑ r : Root n, if r ≤ r0 then rootSignBit p (σ⁻¹ r) else 0) =
        (∑ r : Root n, if r ≤ r0 then rootSignBit p (σ.symm r) else 0) := by
      apply Finset.sum_congr rfl
      intro r _
      rfl
    calc (∑ r : Root n, if r ≤ r0 then rootSignBit p (σ⁻¹ r) else 0)
        = (∑ r : Root n, if r ≤ r0 then rootSignBit p (σ.symm r) else 0) := h_rw_inv
      _ = (∑ r : Root n, if σ.symm r ≤ r0 then rootSignBit p (σ.symm r) else 0) := by
          apply Finset.sum_congr rfl
          intro r _
          exact h_eq_fun r
      _ = ∑ r : Root n, if r ≤ r0 then rootSignBit p r else 0 :=
          Equiv.sum_comp σ.symm
            (fun r => if r ≤ r0 then rootSignBit p r else (0 : ZMod 2))
  have h_inv_eq : inversionSum bitBicharacter (rootPerm (Equiv.swap i j))
        (rootSign p) = ((i.val + k.val : Nat) : ZMod 2) := by
    let r0 := mkRoot i j (adjSwap_ne hij)
    have hq_i : p⁻¹ i = k := by
      calc p⁻¹ i = p⁻¹ (p k) := by rw [hp_k_i]
        _ = k := p.symm_apply_apply k
    have hq_j : p⁻¹ j = l := by
      calc p⁻¹ j = p⁻¹ (p l) := by rw [hp_l_j]
        _ = l := p.symm_apply_apply l
    have h_q_swap : ∀ a : Fin n,
        p⁻¹ (Equiv.swap i j a) = Equiv.swap k l (p⁻¹ a) := by
      intro a
      by_cases ha_i : a = i
      · rw [ha_i, Equiv.swap_apply_left, hq_j, hq_i,
            Equiv.swap_apply_left]
      · by_cases ha_j : a = j
        · rw [ha_j, Equiv.swap_apply_right, hq_i, hq_j,
              Equiv.swap_apply_right]
        · have h_swap : Equiv.swap i j a = a :=
            Equiv.swap_apply_of_ne_of_ne ha_i ha_j
          rw [h_swap]
          have hq_ne_k : p⁻¹ a ≠ k := by
            intro h
            have : a = i := by
              calc a = p (p⁻¹ a) := (p.apply_symm_apply a).symm
                _ = p k := by rw [h]
                _ = i := hp_k_i
            exact ha_i this
          have hq_ne_l : p⁻¹ a ≠ l := by
            intro h
            have : a = j := by
              calc a = p (p⁻¹ a) := (p.apply_symm_apply a).symm
                _ = p l := by rw [h]
                _ = j := hp_l_j
            exact ha_j this
          rw [Equiv.swap_apply_of_ne_of_ne hq_ne_k hq_ne_l]
    have hinv : ∀ r : Root n,
        rootSignBit p (rootPerm (Equiv.swap i j) r) =
          rootSignBit p r := by
      intro r
      have hr0_eq : r0 = (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
        apply Subtype.ext
        simp [r0, mkRoot, min_eq_left (adjSwap_lt hij).le,
          max_eq_right (adjSwap_lt hij).le]
      by_cases hr0 : r = r0
      · rw [hr0, rootPerm_swap_adj_fixed hij]
      · have ha_ne : r.1.1 ≠ i ∨ r.1.2 ≠ j := by
          by_contra h
          push Not at h
          apply hr0
          apply Subtype.ext
          rw [hr0_eq]
          exact Prod.ext h.1 h.2
        have hab : r.1.1 < r.1.2 := r.2
        have hab_val : r.1.1.val < r.1.2.val := Fin.lt_def.mp hab
        have h_not_pair : ¬(r.1.1 = i ∧ r.1.2 = j) := by
          intro ⟨h1, h2⟩
          exact hr0 (Subtype.ext (by rw [hr0_eq]; exact Prod.ext h1 h2))
        have h_swap_lt : Equiv.swap i j r.1.1 < Equiv.swap i j r.1.2 :=
          swap_adj_preserve hij hab h_not_pair
        have h_perm_eq : rootPerm (Equiv.swap i j) r =
            ⟨(Equiv.swap i j r.1.1, Equiv.swap i j r.1.2),
              h_swap_lt⟩ := by
          apply Subtype.ext
          simp only [rootPerm_apply, mkRoot, min_eq_left h_swap_lt.le,
            max_eq_right h_swap_lt.le]
        have hq_a : p⁻¹ (Equiv.swap i j r.1.1) =
            Equiv.swap k l (p⁻¹ r.1.1) := h_q_swap r.1.1
        have hq_b : p⁻¹ (Equiv.swap i j r.1.2) =
            Equiv.swap k l (p⁻¹ r.1.2) := h_q_swap r.1.2
        have hq_ne : ¬(p⁻¹ r.1.1 = k ∧ p⁻¹ r.1.2 = l) := by
          intro ⟨h1, h2⟩
          apply h_not_pair
          constructor
          · calc r.1.1 = p (p⁻¹ r.1.1) := (p.apply_symm_apply _).symm
              _ = p k := by rw [h1]
              _ = i := hp_k_i
          · calc r.1.2 = p (p⁻¹ r.1.2) := (p.apply_symm_apply _).symm
              _ = p l := by rw [h2]
              _ = j := hp_l_j
        have hqa_ne_qb : p⁻¹ r.1.1 ≠ p⁻¹ r.1.2 :=
          p⁻¹.injective.ne (ne_of_lt hab)
        unfold rootSignBit
        rw [h_perm_eq]
        simp only [hq_a, hq_b]
        by_cases hlt : p⁻¹ r.1.1 < p⁻¹ r.1.2
        · have hlt' : Equiv.swap k l (p⁻¹ r.1.1) <
              Equiv.swap k l (p⁻¹ r.1.2) :=
            swap_adj_preserve hkl hlt (fun ⟨h1, h2⟩ => hq_ne ⟨h1, h2⟩)
          rw [ite_eq_left hlt, ite_eq_left hlt']
        · have h_nlt' : ¬Equiv.swap k l (p⁻¹ r.1.1) <
              Equiv.swap k l (p⁻¹ r.1.2) := by
            intro hlt'
            have h_qb_lt_qa : p⁻¹ r.1.2 < p⁻¹ r.1.1 := by
              rcases lt_or_gt_of_ne hqa_ne_qb with h | h
              · exfalso; exact hlt h
              · exact h
            have h_not_pair_rev : ¬(p⁻¹ r.1.2 = k ∧ p⁻¹ r.1.1 = l) := by
              intro ⟨h1, h2⟩
              have hr1 : r.1.2 = i := by
                calc r.1.2 = p (p⁻¹ r.1.2) := (p.apply_symm_apply _).symm
                  _ = p k := by rw [h1]
                  _ = i := hp_k_i
              have hr2 : r.1.1 = j := by
                calc r.1.1 = p (p⁻¹ r.1.1) := (p.apply_symm_apply _).symm
                  _ = p l := by rw [h2]
                  _ = j := hp_l_j
              have : r.1.1 < r.1.2 := hab
              rw [hr2, hr1] at this
              exact not_lt.mpr (le_of_lt (adjSwap_lt hij)) this
            have h_swap_rev : Equiv.swap k l (p⁻¹ r.1.2) <
                Equiv.swap k l (p⁻¹ r.1.1) :=
              swap_adj_preserve hkl h_qb_lt_qa
                (fun ⟨h1, h2⟩ => h_not_pair_rev ⟨h1, h2⟩)
            exact absurd (lt_trans hlt' h_swap_rev) (lt_irrefl _)
          rw [ite_eq_right hlt, ite_eq_right h_nlt']
    have h_parts := inversionSum_swap_adj_eq_parts hij p hinv
    have h_inc_eq := sum_rootIncidence_eq_val p i
    have h_inc_split := sum_rootIncidence_split hij (rootSignBit p)
    have h_sum_inc : (rootsAI i).sum (rootSignBit p) +
        (rootsIB i j).sum (rootSignBit p) =
        (∑ b : Fin n, rootIncidence (rootSignBit p) i b) +
          rootSignBit p r0 := by
      have h1 : (∑ b : Fin n, rootIncidence (rootSignBit p) i b) =
          (rootsAI i).sum (rootSignBit p) + rootSignBit p r0 +
            (rootsIB i j).sum (rootSignBit p) := h_inc_split
      calc (rootsAI i).sum (rootSignBit p) +
            (rootsIB i j).sum (rootSignBit p) =
          ((rootsAI i).sum (rootSignBit p) + rootSignBit p r0 +
              (rootsIB i j).sum (rootSignBit p)) + rootSignBit p r0 := by
            have h2 : (2 : ZMod 2) = 0 := by decide
            have h_char : ∀ x : ZMod 2, x + x = 0 := by
              intro x
              calc x + x = 2 * x := by ring
                _ = 0 := by rw [h2, zero_mul]
            calc (rootsAI i).sum (rootSignBit p) +
                  (rootsIB i j).sum (rootSignBit p) =
                (rootsAI i).sum (rootSignBit p) +
                  (rootsIB i j).sum (rootSignBit p) + 0 := by
                  rw [add_zero]
              _ = (rootsAI i).sum (rootSignBit p) +
                  (rootsIB i j).sum (rootSignBit p) +
                    (rootSignBit p r0 + rootSignBit p r0) := by
                  rw [h_char]
              _ = ((rootsAI i).sum (rootSignBit p) + rootSignBit p r0 +
                  (rootsIB i j).sum (rootSignBit p)) + rootSignBit p r0 := by
                  ring
        _ = (∑ b : Fin n, rootIncidence (rootSignBit p) i b) +
            rootSignBit p r0 := by rw [← h1]
    have h_bit_r0_zero : rootSignBit p r0 = 0 := by
      have hr0_eq : r0 = (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
        apply Subtype.ext
        simp [r0, mkRoot, min_eq_left (adjSwap_lt hij).le,
          max_eq_right (adjSwap_lt hij).le]
      rw [hr0_eq]
      unfold rootSignBit
      have h_lt : p⁻¹ i < p⁻¹ j := by
        rw [hq_i, hq_j]
        exact adjSwap_lt hkl
      rw [ite_eq_left h_lt]
    rw [h_parts, h_sum_inc, h_inc_eq, h_bit_r0_zero, add_zero, hq_i,
      Nat.cast_add]
  have h_par_sum : (∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
        rootSignBit p r else 0) +
      (∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
        rootSignBit p r else 0) =
      (∑ r : Root n, rootSignBit p r) +
        rootSignBit p (mkRoot i j (adjSwap_ne hij)) := by
    let r0 := mkRoot i j (adjSwap_ne hij)
    let f := rootSignBit p
    have h_per : ∀ r : Root n,
        (if r0 ≤ r then f r else 0) + (if r ≤ r0 then f r else 0) =
          f r + if r = r0 then f r else 0 := by
      intro r
      by_cases hr_lt : r < r0
      · have hr_le : r ≤ r0 := le_of_lt hr_lt
        have hr_not_ge : ¬(r0 ≤ r) := not_le.mpr hr_lt
        have hr_ne : r ≠ r0 := ne_of_lt hr_lt
        simp [hr_not_ge, hr_le, hr_ne]
      · by_cases hr_eq : r = r0
        · simp [hr_eq]
        · have hr_gt : r0 < r := by
            have h_le : r0 ≤ r := le_of_not_gt hr_lt
            exact lt_of_le_of_ne h_le (Ne.symm hr_eq)
          have hr_not_le : ¬(r ≤ r0) := not_le.mpr hr_gt
          simp [hr_not_le, le_of_lt hr_gt, hr_eq]
    calc (∑ r : Root n, if r0 ≤ r then f r else 0) +
          (∑ r : Root n, if r ≤ r0 then f r else 0)
        = ∑ r : Root n,
            ((if r0 ≤ r then f r else 0) + (if r ≤ r0 then f r else 0)) := by
          rw [← Finset.sum_add_distrib]
      _ = ∑ r : Root n, (f r + if r = r0 then f r else 0) := by
          apply Finset.sum_congr rfl
          intro r _
          exact h_per r
      _ = (∑ r : Root n, f r) + (∑ r : Root n, if r = r0 then f r else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ r : Root n, f r) + f r0 := by
          have h_sum : (∑ r : Root n, if r = r0 then f r else 0) = f r0 := by
            have h_eq : ∀ r : Root n, (if r = r0 then f r else (0 : ZMod 2)) =
                if r = r0 then f r0 else 0 := by
              intro r
              by_cases hr : r = r0
              · simp [hr]
              · simp [hr]
            calc (∑ r : Root n, if r = r0 then f r else 0)
                = ∑ r : Root n, if r = r0 then f r0 else 0 := by
                  apply Finset.sum_congr rfl
                  intro r _
                  exact h_eq r
              _ = f r0 := by
                  rw [Finset.sum_ite_eq' Finset.univ r0 (fun _ => f r0)]
                  simp
          rw [h_sum]
  have h_bit_r0 : rootSignBit p (mkRoot i j (adjSwap_ne hij)) = 0 := by
    have hq_i : p⁻¹ i = k := by
      calc p⁻¹ i = p⁻¹ (p k) := by rw [hp_k_i]
        _ = k := p.symm_apply_apply k
    have hq_j : p⁻¹ j = l := by
      calc p⁻¹ j = p⁻¹ (p l) := by rw [hp_l_j]
        _ = l := p.symm_apply_apply l
    have hk_lt_l : k < l := by
      apply Fin.lt_def.mpr
      rw [hkl]
      exact Nat.lt_succ_self _
    have h_lt : p⁻¹ i < p⁻¹ j := by rw [hq_i, hq_j]; exact hk_lt_l
    have hr0_eq : mkRoot i j (adjSwap_ne hij) =
        (⟨(i, j), adjSwap_lt hij⟩ : Root n) := by
      apply Subtype.ext
      simp [mkRoot, min_eq_left (adjSwap_lt hij).le,
        max_eq_right (adjSwap_lt hij).le]
    have h_eq : p⁻¹ i < p⁻¹ j := h_lt
    have h_eq2 : p⁻¹ (mkRoot i j (adjSwap_ne hij)).1.1 <
        p⁻¹ (mkRoot i j (adjSwap_ne hij)).1.2 := by
      rw [hr0_eq]
      exact h_eq
    unfold rootSignBit
    rw [ite_eq_left h_eq2]
  have h_root : rootCocycle0 p (Equiv.swap k l) +
      rootCocycle0 (Equiv.swap i j) p =
      parityBit p + ((i.val + k.val : Nat) : ZMod 2) := by
    calc rootCocycle0 p (Equiv.swap k l) + rootCocycle0 (Equiv.swap i j) p
        = (∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
            rootSignBit p r else 0) +
          ((∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
              rootSignBit p ((rootPerm (Equiv.swap i j))⁻¹ r) else 0) +
            inversionSum bitBicharacter (rootPerm (Equiv.swap i j))
              (rootSign p)) := by rw [h_left, h_right_eq]
      _ = (∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
            rootSignBit p r else 0) +
          ((∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
              rootSignBit p r else 0) +
            ((i.val + k.val : Nat) : ZMod 2)) := by
            rw [h_sum_le_eq, h_inv_eq]
      _ = ((∑ r : Root n, if mkRoot i j (adjSwap_ne hij) ≤ r then
              rootSignBit p r else 0) +
            (∑ r : Root n, if r ≤ mkRoot i j (adjSwap_ne hij) then
              rootSignBit p r else 0)) +
            ((i.val + k.val : Nat) : ZMod 2) := by ring
      _ = ((∑ r : Root n, rootSignBit p r) +
            rootSignBit p (mkRoot i j (adjSwap_ne hij))) +
            ((i.val + k.val : Nat) : ZMod 2) := by rw [h_par_sum]
      _ = (∑ r : Root n, rootSignBit p r) +
            ((i.val + k.val : Nat) : ZMod 2) := by
            rw [h_bit_r0, add_zero]
      _ = parityBit p + ((i.val + k.val : Nat) : ZMod 2) := by
            rw [← h_par_eq]
  exact h_root

theorem schurCocycle_neg_overlap {i j k l : Fin n}
    (hij : j.val = i.val + 1) (hkl : l.val = k.val + 1)
    (p : Equiv.Perm (Fin n)) (hp_l_i : p l = i) (hp_k_j : p k = j) :
    schurCocycle p (Equiv.swap k l) +
        schurCocycle (Equiv.swap i j) p =
      parityBit p + ((i.val + k.val + 1 : Nat) : ZMod 2) := by
  let sk : Equiv.Perm (Fin n) := Equiv.swap k l
  let si : Equiv.Perm (Fin n) := Equiv.swap i j
  let q : Equiv.Perm (Fin n) := p * sk
  have h_sk_ne : k ≠ l := adjSwap_ne hkl
  have h_si_ne : i ≠ j := adjSwap_ne hij
  have h_sk_mul : sk * sk = 1 := Equiv.swap_mul_self k l
  have h_si_mul : si * si = 1 := Equiv.swap_mul_self i j
  have hq_k : q k = i := by
    simp only [q, sk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_left, hp_l_i]
  have hq_l : q l = j := by
    simp only [q, sk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_right, hp_k_j]
  have h_pos : schurCocycle q sk + schurCocycle si q =
      parityBit q + ((i.val + k.val : Nat) : ZMod 2) :=
    schurCocycle_pos_overlap hij hkl q hq_k hq_l
  have h_cocycle_p : schurCocycle p sk + schurCocycle q sk = 0 := by
    have h := schurCocycle_cocycle p sk sk
    have hq : p * sk = q := rfl
    rw [hq] at h
    rw [h_sk_mul] at h
    have h_sk_self : schurCocycle sk sk = 0 := by
      simpa [sk] using schurCocycle_swap_self h_sk_ne
    have h_one : schurCocycle p (1 : Equiv.Perm (Fin n)) = 0 :=
      schurCocycle_one_right p
    rw [h_sk_self, h_one, add_zero] at h
    exact h
  have h_si_p_eq : si * p = q := by
    apply Equiv.Perm.ext
    intro x
    simp only [Equiv.Perm.mul_apply, q, si, sk]
    by_cases hx_k : x = k
    · subst hx_k
      rw [hp_k_j, Equiv.swap_apply_right,
        Equiv.swap_apply_left, hp_l_i]
    · by_cases hx_l : x = l
      · subst hx_l
        rw [hp_l_i, Equiv.swap_apply_left,
          Equiv.swap_apply_right, hp_k_j]
      · have hpx_ne_i : p x ≠ i := by
          intro h
          have : x = l := p.injective (h.trans hp_l_i.symm)
          exact hx_l this
        have hpx_ne_j : p x ≠ j := by
          intro h
          have : x = k := p.injective (h.trans hp_k_j.symm)
          exact hx_k this
        have h_si : si (p x) = p x :=
          Equiv.swap_apply_of_ne_of_ne hpx_ne_i hpx_ne_j
        have h_sk : sk x = x :=
          Equiv.swap_apply_of_ne_of_ne hx_k hx_l
        rw [h_si, h_sk]
  have h_cocycle_si : schurCocycle si p + schurCocycle si q = 0 := by
    have h := schurCocycle_cocycle si si p
    rw [h_si_mul, h_si_p_eq] at h
    have h_si_self : schurCocycle si si = 0 := by
      simpa [si] using schurCocycle_swap_self h_si_ne
    have h_one : schurCocycle (1 : Equiv.Perm (Fin n)) p = 0 :=
      schurCocycle_one_left p
    rw [h_si_self, h_one, zero_add] at h
    exact h.symm
  have h_char : ∀ x : ZMod 2, x + x = 0 := by
    intro x
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc x + x = 2 * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  have h_parity_q : parityBit q = parityBit p + 1 := by
    calc parityBit q = parityBit (p * sk) := rfl
      _ = parityBit p + parityBit sk := parityBit_mul p sk
      _ = parityBit p + 1 := by rw [parityBit_swap_adj hkl]
  have h_S_eq : schurCocycle p sk + schurCocycle si p =
      schurCocycle q sk + schurCocycle si q := by
    have h_sum_zero :
        (schurCocycle p sk + schurCocycle si p) +
          (schurCocycle q sk + schurCocycle si q) = 0 := by
      calc (schurCocycle p sk + schurCocycle si p) +
            (schurCocycle q sk + schurCocycle si q)
          = (schurCocycle p sk + schurCocycle q sk) +
            (schurCocycle si p + schurCocycle si q) := by ring
        _ = 0 + 0 := by rw [h_cocycle_p, h_cocycle_si]
        _ = 0 := by simp
    calc schurCocycle p sk + schurCocycle si p
        = schurCocycle p sk + schurCocycle si p + 0 := by simp
      _ = schurCocycle p sk + schurCocycle si p +
          ((schurCocycle q sk + schurCocycle si q) +
            (schurCocycle q sk + schurCocycle si q)) := by
          rw [h_char (schurCocycle q sk + schurCocycle si q)]
      _ = (schurCocycle p sk + schurCocycle si p +
          (schurCocycle q sk + schurCocycle si q)) +
          (schurCocycle q sk + schurCocycle si q) := by ring
      _ = 0 + (schurCocycle q sk + schurCocycle si q) := by
          rw [h_sum_zero]
      _ = schurCocycle q sk + schurCocycle si q := by simp
  have h_cast : ((i.val + k.val + 1 : Nat) : ZMod 2) =
      ((i.val + k.val : Nat) : ZMod 2) + 1 := by
    have h1 : (i.val + k.val + 1 : Nat) = (i.val + k.val) + 1 := rfl
    rw [h1, Nat.cast_add, Nat.cast_one]
  calc schurCocycle p (Equiv.swap k l) + schurCocycle (Equiv.swap i j) p
      = schurCocycle p sk + schurCocycle si p := by rfl
    _ = schurCocycle q sk + schurCocycle si q := h_S_eq
    _ = parityBit q + ((i.val + k.val : Nat) : ZMod 2) := h_pos
    _ = parityBit p + 1 + ((i.val + k.val : Nat) : ZMod 2) := by
        rw [h_parity_q]
    _ = parityBit p + (((i.val + k.val : Nat) : ZMod 2) + 1) := by ring
    _ = parityBit p + ((i.val + k.val + 1 : Nat) : ZMod 2) := by
        rw [h_cast]

end AdjacentOverlap

end PermutationSchurCocycle

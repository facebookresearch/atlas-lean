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

public import MathlibExt.GroupTheory.PermutationSchurCocycle

/-!
# Root transport and overlap classification for finite permutations

A permutation sends an increasing root to another increasing root and may
preserve or reverse its orientation.  `RootTransport` packages the landed
`rootPerm` and `rootSignBit` data.  `RootOverlapClass` gives the corresponding
three-way comparison with a requested target root: positive orientation,
negative orientation, or a different transported root.

The classifier is computable.  Its multiplication law follows the exact
permutation convention `(p * q) x = p (q x)`, and coefficient naturality says
that mapping a monomial base changes its weight tuple but not this
classification.  No global decidability instance or new permutation action is
introduced.
-/

@[expose] public section

set_option autoImplicit false

namespace PermutationSchurCocycle

open PermutationBilinearCocycle

universe u v

variable {n : ℕ}

/-- The increasing root and orientation bit obtained by transporting a root
through a permutation.  The bit is evaluated at the transported root, so zero
means that the source order is preserved and one means that it is reversed. -/
@[ext]
structure RootTransport (n : ℕ) where
  root : Root n
  orientation : ZMod 2

/-- Transport a root through a permutation, retaining its orientation bit. -/
noncomputable def rootTransport (p : Equiv.Perm (Fin n)) (r : Root n) : RootTransport n where
  root := rootPerm p r
  orientation := rootSignBit p (rootPerm p r)

@[simp]
theorem rootTransport_root (p : Equiv.Perm (Fin n)) (r : Root n) :
    (rootTransport p r).root = rootPerm p r :=
  rfl

@[simp]
theorem rootTransport_orientation (p : Equiv.Perm (Fin n)) (r : Root n) :
    (rootTransport p r).orientation = rootSignBit p (rootPerm p r) :=
  rfl

@[simp]
theorem rootSignBit_one (r : Root n) :
    rootSignBit (1 : Equiv.Perm (Fin n)) r = 0 := by
  unfold rootSignBit
  simp [r.2]

/-- Identity transport fixes a root with positive orientation. -/
@[simp]
theorem rootTransport_one (r : Root n) :
    rootTransport (1 : Equiv.Perm (Fin n)) r =
      { root := r, orientation := 0 } := by
  apply RootTransport.ext
  · exact DFunLike.congr_fun rootPerm_one r
  · simp [rootTransport]

/-- Composition of root transports.  The inner transport `q` acts first and
the two orientation bits add in `ZMod 2`. -/
theorem rootTransport_mul (p q : Equiv.Perm (Fin n)) (r : Root n) :
    rootTransport (p * q) r =
      { root := rootPerm p (rootPerm q r)
        orientation :=
          (rootTransport p (rootPerm q r)).orientation +
            (rootTransport q r).orientation } := by
  apply RootTransport.ext
  · exact DFunLike.congr_fun (rootPerm_mul p q) r
  · change rootSignBit (p * q) (rootPerm (p * q) r) =
      rootSignBit p (rootPerm p (rootPerm q r)) +
        rootSignBit q (rootPerm q r)
    have hroot : rootPerm (p * q) r = rootPerm p (rootPerm q r) :=
      DFunLike.congr_fun (rootPerm_mul p q) r
    rw [hroot]
    have hmul := rootSignBit_mul (p := p) (q := q)
      (rootPerm p (rootPerm q r))
    have hinv : (rootPerm p)⁻¹ (rootPerm p (rootPerm q r)) = rootPerm q r :=
      (rootPerm p).symm_apply_apply (rootPerm q r)
    rw [hinv] at hmul
    exact hmul

/-- Inverting a permutation reverses a root transport without changing its
orientation bit. -/
theorem rootTransport_inv (p : Equiv.Perm (Fin n)) (r : Root n) :
    rootTransport p⁻¹ (rootPerm p r) =
      { root := r, orientation := (rootTransport p r).orientation } := by
  have hmul := rootTransport_mul p⁻¹ p r
  rw [inv_mul_cancel, rootTransport_one] at hmul
  apply RootTransport.ext
  · exact (congrArg RootTransport.root hmul).symm
  · have horient := congrArg RootTransport.orientation hmul
    have hsum :
        (rootTransport p⁻¹ (rootPerm p r)).orientation +
            (rootTransport p r).orientation = 0 := by
      exact horient.symm
    have hnegOne : (-1 : ZMod 2) = 1 := by decide
    calc
      (rootTransport p⁻¹ (rootPerm p r)).orientation =
          -(rootTransport p r).orientation :=
        eq_neg_of_add_eq_zero_left hsum
      _ = (-1 : ZMod 2) * (rootTransport p r).orientation := by ring
      _ = (rootTransport p r).orientation := by rw [hnegOne, one_mul]

/-- The three possible relations between a transported source root and a
target root. -/
inductive RootOverlapClass
  | none
  | positive
  | negative
deriving DecidableEq, Repr

namespace RootOverlapClass

/-- Composition of overlap orientations.  `none` is absorbing, `positive` is
neutral, and two negative orientations compose to positive. -/
def comp : RootOverlapClass → RootOverlapClass → RootOverlapClass
  | none, _ => none
  | _, none => none
  | positive, x => x
  | negative, positive => negative
  | negative, negative => positive

/-- Reverse the orientation of a nonempty overlap. -/
def flip : RootOverlapClass → RootOverlapClass
  | none => none
  | positive => negative
  | negative => positive

@[simp] theorem none_comp (c : RootOverlapClass) : comp none c = none := rfl
@[simp] theorem comp_none (c : RootOverlapClass) : comp c none = none := by cases c <;> rfl
@[simp] theorem positive_comp (c : RootOverlapClass) : comp positive c = c := by cases c <;> rfl
@[simp] theorem comp_positive (c : RootOverlapClass) : comp c positive = c := by cases c <;> rfl
@[simp] theorem negative_comp_negative : comp negative negative = positive := rfl
@[simp] theorem flip_none : flip none = none := rfl
@[simp] theorem flip_positive : flip positive = negative := rfl
@[simp] theorem flip_negative : flip negative = positive := rfl
@[simp] theorem flip_flip (c : RootOverlapClass) : flip (flip c) = c := by cases c <;> rfl
@[simp] theorem comp_negative (c : RootOverlapClass) : comp c negative = flip c := by
  cases c <;> rfl

@[simp] theorem negative_comp (c : RootOverlapClass) : comp negative c = flip c := by
  cases c <;> rfl

end RootOverlapClass

/-- Classify how `p` sends the ordered endpoints of `source` relative to the
ordered endpoints of `target`. -/
def rootOverlapClass (p : Equiv.Perm (Fin n))
    (target source : Root n) : RootOverlapClass :=
  if p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2 then
    .positive
  else if p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1 then
    .negative
  else
    .none

private theorem positive_negative_disjoint
    (p : Equiv.Perm (Fin n)) (target source : Root n) :
    ¬ ((p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2) ∧
      (p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1)) := by
  rintro ⟨hpos, hneg⟩
  exact target.2.ne (hpos.1.symm.trans hneg.1)

theorem rootOverlapClass_eq_positive_iff
    (p : Equiv.Perm (Fin n)) (target source : Root n) :
    rootOverlapClass p target source = .positive ↔
      p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2 := by
  by_cases hpos : p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2
  · have hclass : rootOverlapClass p target source = .positive := by
      unfold rootOverlapClass
      simp [hpos]
    exact ⟨fun _ => hpos, fun _ => hclass⟩
  · by_cases hneg : p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1
    · have hclass : rootOverlapClass p target source = .negative := by
        unfold rootOverlapClass
        simp [hneg, target.2.ne, target.2.ne']
      constructor
      · intro hEq
        rw [hclass] at hEq
        contradiction
      · intro hp
        exact (hpos hp).elim
    · have hclass : rootOverlapClass p target source = .none := by
        unfold rootOverlapClass
        simp [hpos, hneg]
      constructor
      · intro hEq
        rw [hclass] at hEq
        contradiction
      · intro hp
        exact (hpos hp).elim

theorem rootOverlapClass_eq_negative_iff
    (p : Equiv.Perm (Fin n)) (target source : Root n) :
    rootOverlapClass p target source = .negative ↔
      p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1 := by
  by_cases hpos : p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2
  · have hclass : rootOverlapClass p target source = .positive := by
      unfold rootOverlapClass
      simp [hpos]
    constructor
    · intro hEq
      rw [hclass] at hEq
      contradiction
    · intro hneg
      exact (positive_negative_disjoint p target source ⟨hpos, hneg⟩).elim
  · by_cases hneg : p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1
    · have hclass : rootOverlapClass p target source = .negative := by
        unfold rootOverlapClass
        simp [hneg, target.2.ne, target.2.ne']
      exact ⟨fun _ => hneg, fun _ => hclass⟩
    · have hclass : rootOverlapClass p target source = .none := by
        unfold rootOverlapClass
        simp [hpos, hneg]
      constructor
      · intro hEq
        rw [hclass] at hEq
        contradiction
      · intro hn
        exact (hneg hn).elim

theorem rootOverlapClass_eq_none_iff
    (p : Equiv.Perm (Fin n)) (target source : Root n) :
    rootOverlapClass p target source = .none ↔
      ¬ (p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2) ∧
      ¬ (p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1) := by
  by_cases hpos : p source.1.1 = target.1.1 ∧ p source.1.2 = target.1.2
  · have hclass : rootOverlapClass p target source = .positive := by
      unfold rootOverlapClass
      simp [hpos]
    constructor
    · intro hEq
      rw [hclass] at hEq
      contradiction
    · rintro ⟨hnpos, _⟩
      exact (hnpos hpos).elim
  · by_cases hneg : p source.1.1 = target.1.2 ∧ p source.1.2 = target.1.1
    · have hclass : rootOverlapClass p target source = .negative := by
        unfold rootOverlapClass
        simp [hneg, target.2.ne, target.2.ne']
      constructor
      · intro hEq
        rw [hclass] at hEq
        contradiction
      · rintro ⟨_, hnneg⟩
        exact (hnneg hneg).elim
    · have hclass : rootOverlapClass p target source = .none := by
        unfold rootOverlapClass
        simp [hpos, hneg]
      exact ⟨fun _ => ⟨hpos, hneg⟩, fun _ => hclass⟩

/-- A root is an overlap with itself under the identity permutation. -/
@[simp]
theorem rootOverlapClass_one_self (r : Root n) :
    rootOverlapClass (1 : Equiv.Perm (Fin n)) r r = .positive := by
  rw [rootOverlapClass_eq_positive_iff]
  simp

/-- Identity classification is positive exactly on equal roots and otherwise
has no overlap. -/
theorem rootOverlapClass_one (target source : Root n) :
    rootOverlapClass (1 : Equiv.Perm (Fin n)) target source =
      if source = target then .positive else .none := by
  by_cases h : source = target
  · subst target
    simp
  · have hpos : ¬ (source.1.1 = target.1.1 ∧ source.1.2 = target.1.2) := by
      intro hp
      exact h (Subtype.ext (Prod.ext hp.1 hp.2))
    have hneg : ¬ (source.1.1 = target.1.2 ∧ source.1.2 = target.1.1) := by
      rintro ⟨h₁, h₂⟩
      have : target.1.2 < target.1.1 := by
        calc
          target.1.2 = source.1.1 := h₁.symm
          _ < source.1.2 := source.2
          _ = target.1.1 := h₂
      exact (not_lt_of_ge target.2.le) this
    simp only [h, ite_false]
    rw [rootOverlapClass_eq_none_iff]
    simpa using And.intro hpos hneg

private theorem rootOverlapClass_ext
    {a b : RootOverlapClass}
    (hpos : (a = .positive) ↔ (b = .positive))
    (hneg : (a = .negative) ↔ (b = .negative)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Root-overlap classification is invariant under pointwise-equal
permutations. -/
theorem rootOverlapClass_congr
    {p q : Equiv.Perm (Fin n)}
    (h : ∀ x, p x = q x) (target source : Root n) :
    rootOverlapClass p target source = rootOverlapClass q target source := by
  have hpq : p = q := Equiv.ext h
  rw [hpq]

/-- Inverse transport exchanges the source and target without changing the
overlap orientation. -/
theorem rootOverlapClass_inv (p : Equiv.Perm (Fin n))
    (target source : Root n) :
    rootOverlapClass p⁻¹ source target = rootOverlapClass p target source := by
  apply rootOverlapClass_ext
  · rw [rootOverlapClass_eq_positive_iff,
      rootOverlapClass_eq_positive_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor
      · simpa using (congrArg p h₁).symm
      · simpa using (congrArg p h₂).symm
    · rintro ⟨h₁, h₂⟩
      constructor
      · simpa using (congrArg p.symm h₁).symm
      · simpa using (congrArg p.symm h₂).symm
  · rw [rootOverlapClass_eq_negative_iff,
      rootOverlapClass_eq_negative_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor
      · simpa using (congrArg p h₂).symm
      · simpa using (congrArg p h₁).symm
    · rintro ⟨h₁, h₂⟩
      constructor
      · simpa using (congrArg p.symm h₂).symm
      · simpa using (congrArg p.symm h₁).symm

/-- Root-overlap classification composes with permutation multiplication. -/
theorem rootOverlapClass_mul (p q : Equiv.Perm (Fin n))
    (target source : Root n) :
    rootOverlapClass (p * q) target source =
      RootOverlapClass.comp
        (rootOverlapClass p target (rootPerm q source))
        (rootOverlapClass q (rootPerm q source) source) := by
  by_cases hq : q source.1.1 < q source.1.2
  · have hroot : rootPerm q source =
        (⟨(q source.1.1, q source.1.2), hq⟩ : Root n) := by
      simpa only [rootPerm_apply] using (mkRoot_of_lt hq)
    have hinner : rootOverlapClass q (rootPerm q source) source = .positive := by
      rw [rootOverlapClass_eq_positive_iff, hroot]
      exact ⟨rfl, rfl⟩
    rw [hinner, RootOverlapClass.comp_positive]
    apply rootOverlapClass_ext
    · rw [rootOverlapClass_eq_positive_iff,
        rootOverlapClass_eq_positive_iff, hroot]
      rfl
    · rw [rootOverlapClass_eq_negative_iff,
        rootOverlapClass_eq_negative_iff, hroot]
      rfl
  · have hq' : q source.1.2 < q source.1.1 :=
      lt_of_le_of_ne (le_of_not_gt hq)
        (q.injective.ne source.2.ne).symm
    have hroot : rootPerm q source =
        (⟨(q source.1.2, q source.1.1), hq'⟩ : Root n) := by
      simpa only [rootPerm_apply] using (mkRoot_of_gt hq')
    have hinner : rootOverlapClass q (rootPerm q source) source = .negative := by
      rw [rootOverlapClass_eq_negative_iff, hroot]
      exact ⟨rfl, rfl⟩
    rw [hinner, RootOverlapClass.comp_negative]
    let outer := rootOverlapClass p target (rootPerm q source)
    have hpos : rootOverlapClass (p * q) target source = .positive ↔
        RootOverlapClass.flip outer = .positive := by
      rw [rootOverlapClass_eq_positive_iff]
      change (p (q source.1.1) = target.1.1 ∧
          p (q source.1.2) = target.1.2) ↔ _
      rw [show RootOverlapClass.flip outer = .positive ↔ outer = .negative by
        cases outer <;> simp [RootOverlapClass.flip]]
      dsimp only [outer]
      rw [rootOverlapClass_eq_negative_iff, hroot]
      exact and_comm
    have hneg : rootOverlapClass (p * q) target source = .negative ↔
        RootOverlapClass.flip outer = .negative := by
      rw [rootOverlapClass_eq_negative_iff]
      change (p (q source.1.1) = target.1.2 ∧
          p (q source.1.2) = target.1.1) ↔ _
      rw [show RootOverlapClass.flip outer = .negative ↔ outer = .positive by
        cases outer <;> simp [RootOverlapClass.flip]]
      dsimp only [outer]
      rw [rootOverlapClass_eq_positive_iff, hroot]
      exact and_comm
    exact rootOverlapClass_ext hpos hneg

/-- Multiplying on the left by the swap of the target endpoints reverses a
root-overlap orientation. -/
theorem rootOverlapClass_left_swap (p : Equiv.Perm (Fin n))
    (target source : Root n) :
    rootOverlapClass (Equiv.swap target.1.1 target.1.2 * p) target source =
      RootOverlapClass.flip (rootOverlapClass p target source) := by
  apply rootOverlapClass_ext
  · rw [rootOverlapClass_eq_positive_iff]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [show RootOverlapClass.flip (rootOverlapClass p target source) = .positive ↔
        rootOverlapClass p target source = .negative by
      cases rootOverlapClass p target source <;> simp [RootOverlapClass.flip]]
    rw [rootOverlapClass_eq_negative_iff]
  · rw [rootOverlapClass_eq_negative_iff]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [show RootOverlapClass.flip (rootOverlapClass p target source) = .negative ↔
        rootOverlapClass p target source = .positive by
      cases rootOverlapClass p target source <;> simp [RootOverlapClass.flip]]
    rw [rootOverlapClass_eq_positive_iff]

/-- Multiplying on the right by the swap of the source endpoints reverses a
root-overlap orientation. -/
theorem rootOverlapClass_right_swap (p : Equiv.Perm (Fin n))
    (target source : Root n) :
    rootOverlapClass (p * Equiv.swap source.1.1 source.1.2) target source =
      RootOverlapClass.flip (rootOverlapClass p target source) := by
  apply rootOverlapClass_ext
  · rw [rootOverlapClass_eq_positive_iff]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    rw [show RootOverlapClass.flip (rootOverlapClass p target source) = .positive ↔
        rootOverlapClass p target source = .negative by
      cases rootOverlapClass p target source <;> simp [RootOverlapClass.flip]]
    rw [rootOverlapClass_eq_negative_iff]
    exact and_comm
  · rw [rootOverlapClass_eq_negative_iff]
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    rw [show RootOverlapClass.flip (rootOverlapClass p target source) = .negative ↔
        rootOverlapClass p target source = .positive by
      cases rootOverlapClass p target source <;> simp [RootOverlapClass.flip]]
    rw [rootOverlapClass_eq_positive_iff]
    exact and_comm

/-- The root associated to an adjacent increasing pair. -/
def adjacentRoot {i j : Fin n} (hij : i ⋖ j) : Root n :=
  ⟨(i, j), hij.lt⟩

/-- Three-way overlap classifier for two adjacent increasing pairs. -/
def adjacentOverlapClass (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) : RootOverlapClass :=
  rootOverlapClass p (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_eq_positive_iff
    (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass p hij hkl = .positive ↔
      p k = i ∧ p l = j :=
  rootOverlapClass_eq_positive_iff p (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_eq_negative_iff
    (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass p hij hkl = .negative ↔
      p k = j ∧ p l = i :=
  rootOverlapClass_eq_negative_iff p (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_eq_none_iff
    (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass p hij hkl = .none ↔
      ¬ (p k = i ∧ p l = j) ∧ ¬ (p k = j ∧ p l = i) :=
  rootOverlapClass_eq_none_iff p (adjacentRoot hij) (adjacentRoot hkl)

@[simp]
theorem adjacentOverlapClass_one_self
    {i j : Fin n} (hij : i ⋖ j) :
    adjacentOverlapClass (1 : Equiv.Perm (Fin n)) hij hij = .positive :=
  rootOverlapClass_one_self (adjacentRoot hij)

theorem adjacentOverlapClass_mul (p q : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    rootOverlapClass (p * q) (adjacentRoot hij) (adjacentRoot hkl) =
      RootOverlapClass.comp
        (rootOverlapClass p (adjacentRoot hij)
          (rootPerm q (adjacentRoot hkl)))
        (rootOverlapClass q (rootPerm q (adjacentRoot hkl))
          (adjacentRoot hkl)) :=
  rootOverlapClass_mul p q (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_inv (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass p⁻¹ hkl hij = adjacentOverlapClass p hij hkl :=
  rootOverlapClass_inv p (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_left_swap (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass (Equiv.swap i j * p) hij hkl =
      RootOverlapClass.flip (adjacentOverlapClass p hij hkl) :=
  rootOverlapClass_left_swap p (adjacentRoot hij) (adjacentRoot hkl)

theorem adjacentOverlapClass_right_swap (p : Equiv.Perm (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass (p * Equiv.swap k l) hij hkl =
      RootOverlapClass.flip (adjacentOverlapClass p hij hkl) :=
  rootOverlapClass_right_swap p (adjacentRoot hij) (adjacentRoot hkl)

/-- Mapping monomial coefficients does not change root-overlap
classification, because `monomialBaseHom` preserves the permutation
coordinate. -/
@[simp]
theorem rootOverlapClass_monomialBaseHom
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) (M : MonomialBase A (Fin n))
    (target source : Root n) :
    rootOverlapClass (monomialBaseHom f M).right target source =
      rootOverlapClass M.right target source := by
  rw [monomialBaseHom_right]

@[simp]
theorem adjacentOverlapClass_monomialBaseHom
    {A : Type u} {B : Type v} [Group A] [Group B]
    (f : A →* B) (M : MonomialBase A (Fin n))
    {i j k l : Fin n} (hij : i ⋖ j) (hkl : k ⋖ l) :
    adjacentOverlapClass (monomialBaseHom f M).right hij hkl =
      adjacentOverlapClass M.right hij hkl := by
  rw [monomialBaseHom_right]

end PermutationSchurCocycle

end

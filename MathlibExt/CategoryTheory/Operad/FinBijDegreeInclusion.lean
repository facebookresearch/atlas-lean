/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Monoidal.Sequence.Index
public import MathlibExt.CategoryTheory.Operad.FinBijCard
public import MathlibExt.CategoryTheory.Operad.FinBijSmallEquiv

/-!
# Finite coordinates and ordered degrees in the finite-bijection groupoid

The finite coordinate maps retain identities, compositions, ordered blocks,
associators, unitors, and braidings. The discrete natural-number degree index enters the small
finite-bijection groupoid with identity labels and a named strong monoidal structure.
Every index arrow and its finite coordinates are retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

namespace CategoryTheory.Operad.SmallFinBijGroupoid

local notation "N" => CategoryTheory.Sequence.Index
local notation "I" => SmallFinBijGroupoid

/-- The ordered direct sum of two finite bijections. -/
abbrev finiteBijectionSum {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q) :
    Fin (m + p) ≃ Fin (n + q) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

/-- The first ordered block retains its original source coordinates. -/
theorem finiteBijectionSum_left {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q)
    (i : Fin m) :
    finiteBijectionSum e f (Fin.castAdd p i) = Fin.castAdd q (e i) := by
  simp [finiteBijectionSum]

/-- The second ordered block follows the first without reversing it. -/
theorem finiteBijectionSum_right {m n p q : ℕ} (e : Fin m ≃ Fin n) (f : Fin p ≃ Fin q)
    (i : Fin p) :
    finiteBijectionSum e f (Fin.natAdd m i) = Fin.natAdd n (f i) := by
  simp [finiteBijectionSum]


/-- The actual original symmetric tensor map acts by the same ordered finite direct sum. -/
theorem smallEquivOfHom_tensor {A A' B B' : SmallFinBijGroupoid}
    (f : A ⟶ A') (g : B ⟶ B') :
    smallEquivOfHom (f ⊗ₘ g) =
      finiteBijectionSum (smallEquivOfHom f) (smallEquivOfHom g) := by
  let split (p q : ℕ) : ULift.{0, 0} (Fin (p + q)) ≃
      ULift.{0, 0} (Fin p) ⊕ ULift.{0, 0} (Fin q) :=
    Equiv.ulift.trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))
  let unlift {p q : ℕ} (e : ULift.{0, 0} (Fin p) ≃ ULift.{0, 0} (Fin q)) :
      Fin p ≃ Fin q := Equiv.ulift.symm.trans (e.trans Equiv.ulift)
  have hBlock {p p' q q' : ℕ}
      (e : ULift.{0, 0} (Fin p) ≃ ULift.{0, 0} (Fin p'))
      (d : ULift.{0, 0} (Fin q) ≃ ULift.{0, 0} (Fin q')) :
      unlift ((split p q).trans ((Equiv.sumCongr e d).trans (split p' q').symm)) =
        finiteBijectionSum (unlift e) (unlift d) := by
    apply Equiv.ext
    intro i
    rcases hq : finSumFinEquiv.symm i with a | b
    · have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      subst i
      apply Fin.ext
      dsimp only [unlift, split, finiteBijectionSum, Equiv.trans_apply]
      simp only [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
        finSumFinEquiv_apply_left]
      simp
    · have hi := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hi
      subst i
      apply Fin.ext
      dsimp only [unlift, split, finiteBijectionSum, Equiv.trans_apply]
      simp only [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
        finSumFinEquiv_apply_right]
      simp
  change unlift (FinBijGroupoid.equivOfHom
    (smallFinBijEquivalence.functor.map (SmallFinBijGroupoid.blockSumHom f g))) = _
  rw [SmallFinBijGroupoid.blockSumHom_equivOfHom]
  exact hBlock _ _


private def liftedFiniteSplit (p q : ℕ) :
    ULift.{0, 0} (Fin (p + q)) ≃ ULift.{0, 0} (Fin p) ⊕ ULift.{0, 0} (Fin q) :=
  Equiv.ulift.trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr Equiv.ulift.symm Equiv.ulift.symm))

private theorem liftedFiniteSplit_apply (p q : ℕ) (i : Fin (p + q)) :
    liftedFiniteSplit p q (ULift.up i) =
      Sum.map ULift.up ULift.up (finSumFinEquiv.symm i) := rfl

private theorem liftedFiniteSplit_symm_apply (p q : ℕ) (z : Fin p ⊕ Fin q) :
    (liftedFiniteSplit p q).symm (Sum.map ULift.up ULift.up z) =
      ULift.up (finSumFinEquiv z) := by
  cases z <;> rfl

/-- The original source associator is the literal finite-coordinate reassociation. -/
theorem smallEquivOfHom_associator (A B C : SmallFinBijGroupoid) :
    smallEquivOfHom (α_ A B C).hom =
      finCongr (Nat.add_assoc A.of.len B.of.len C.of.len) := by
  let assocE : ULift.{0, 0} (Fin ((A.of.len + B.of.len) + C.of.len)) ≃
      ULift.{0, 0} (Fin (A.of.len + (B.of.len + C.of.len))) :=
    (liftedFiniteSplit (A.of.len + B.of.len) C.of.len).trans <|
      (Equiv.sumCongr (liftedFiniteSplit A.of.len B.of.len) (Equiv.refl _)).trans <|
        (Equiv.sumAssoc _ _ _).trans <|
          (Equiv.sumCongr (Equiv.refl _)
            (liftedFiniteSplit B.of.len C.of.len).symm).trans
            (liftedFiniteSplit A.of.len (B.of.len + C.of.len)).symm
  have hRaw :
      (show ULift.{0, 0} (Fin ((A.of.len + B.of.len) + C.of.len)) →
          ULift.{0, 0} (Fin (A.of.len + (B.of.len + C.of.len))) from
        (α_ A B C).hom.iso.hom) = assocE := rfl
  apply Equiv.ext
  intro i
  change Fin ((A.of.len + B.of.len) + C.of.len) at i
  apply Fin.ext
  change (((show ULift.{0, 0} (Fin ((A.of.len + B.of.len) + C.of.len)) →
      ULift.{0, 0} (Fin (A.of.len + (B.of.len + C.of.len))) from
      (α_ A B C).hom.iso.hom) (ULift.up i)).down).val = i.val
  rw [hRaw]
  dsimp only [assocE, Equiv.trans_apply]
  rcases hq : finSumFinEquiv.symm i with ab | c
  · rcases hab : finSumFinEquiv.symm ab with a | b
    · rw [show liftedFiniteSplit (A.of.len + B.of.len) C.of.len (ULift.up i) =
          Sum.inl (ULift.up ab) by rw [liftedFiniteSplit_apply, hq]; rfl]
      simp only [Equiv.sumCongr_apply, Sum.map_inl]
      rw [show liftedFiniteSplit A.of.len B.of.len (ULift.up ab) =
          Sum.inl (ULift.up a) by rw [liftedFiniteSplit_apply, hab]; rfl]
      simp only [Sum.map_inl, Equiv.sumAssoc_apply_inl_inl, Equiv.refl_apply]
      rw [show (liftedFiniteSplit A.of.len (B.of.len + C.of.len)).symm
          (Sum.inl (ULift.up a)) = ULift.up (Fin.castAdd (B.of.len + C.of.len) a) by
        simpa using liftedFiniteSplit_symm_apply A.of.len (B.of.len + C.of.len) (Sum.inl a)]
      have hOuter := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hOuter
      have hInner := finSumFinEquiv.apply_symm_apply ab
      rw [hab] at hInner
      have ho : ab.val = i.val := by simpa using congrArg Fin.val hOuter
      have hi : a.val = ab.val := by simpa using congrArg Fin.val hInner
      exact hi.trans ho
    · rw [show liftedFiniteSplit (A.of.len + B.of.len) C.of.len (ULift.up i) =
          Sum.inl (ULift.up ab) by rw [liftedFiniteSplit_apply, hq]; rfl]
      simp only [Equiv.sumCongr_apply, Sum.map_inl]
      rw [show liftedFiniteSplit A.of.len B.of.len (ULift.up ab) =
          Sum.inr (ULift.up b) by rw [liftedFiniteSplit_apply, hab]; rfl]
      simp only [Sum.map_inr, Equiv.sumAssoc_apply_inl_inr]
      rw [show (liftedFiniteSplit B.of.len C.of.len).symm (Sum.inl (ULift.up b)) =
          ULift.up (finSumFinEquiv (Sum.inl b)) by
        simpa using liftedFiniteSplit_symm_apply B.of.len C.of.len (Sum.inl b)]
      rw [show (liftedFiniteSplit A.of.len (B.of.len + C.of.len)).symm
          (Sum.inr (ULift.up (finSumFinEquiv (Sum.inl b)))) =
            ULift.up (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl b)))) by
        simpa using liftedFiniteSplit_symm_apply A.of.len (B.of.len + C.of.len)
          (Sum.inr (finSumFinEquiv (Sum.inl b)))]
      have hOuter := finSumFinEquiv.apply_symm_apply i
      rw [hq] at hOuter
      have hInner := finSumFinEquiv.apply_symm_apply ab
      rw [hab] at hInner
      have ho : ab.val = i.val := by simpa using congrArg Fin.val hOuter
      have hi : A.of.len + b.val = ab.val := by simpa using congrArg Fin.val hInner
      simpa using hi.trans ho
  · rw [show liftedFiniteSplit (A.of.len + B.of.len) C.of.len (ULift.up i) =
        Sum.inr (ULift.up c) by rw [liftedFiniteSplit_apply, hq]; rfl]
    simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumAssoc_apply_inr, Equiv.refl_apply]
    rw [show (liftedFiniteSplit B.of.len C.of.len).symm (Sum.inr (ULift.up c)) =
        ULift.up (finSumFinEquiv (Sum.inr c)) by
      simpa using liftedFiniteSplit_symm_apply B.of.len C.of.len (Sum.inr c)]
    rw [show (liftedFiniteSplit A.of.len (B.of.len + C.of.len)).symm
        (Sum.inr (ULift.up (finSumFinEquiv (Sum.inr c)))) =
          ULift.up (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr c)))) by
      simpa using liftedFiniteSplit_symm_apply A.of.len (B.of.len + C.of.len)
        (Sum.inr (finSumFinEquiv (Sum.inr c)))]
    have hi := finSumFinEquiv.apply_symm_apply i
    rw [hq] at hi
    simpa [Nat.add_assoc] using congrArg Fin.val hi

/-- The left source unitor deletes the actual empty finite block. -/
theorem smallEquivOfHom_leftUnitor (A : SmallFinBijGroupoid) :
    smallEquivOfHom (λ_ A).hom = finCongr (Nat.zero_add A.of.len) := by
  let _ : IsEmpty (ULift.{0, 0} (Fin 0)) := ⟨fun z => Fin.elim0 z.down⟩
  let leftE := (liftedFiniteSplit 0 A.of.len).trans (Equiv.emptySum _ _)
  have hRaw :
      (show ULift.{0, 0} (Fin (0 + A.of.len)) → ULift.{0, 0} (Fin A.of.len) from
        (λ_ A).hom.iso.hom) = leftE := rfl
  apply Equiv.ext
  intro i
  change Fin (0 + A.of.len) at i
  apply Fin.ext
  change (((show ULift.{0, 0} (Fin (0 + A.of.len)) → ULift.{0, 0} (Fin A.of.len) from
    (λ_ A).hom.iso.hom) (ULift.up i)).down).val = i.val
  rw [hRaw]
  dsimp only [leftE, Equiv.trans_apply]
  rcases hq : finSumFinEquiv.symm i with z | a
  · exact Fin.elim0 z
  · rw [show liftedFiniteSplit 0 A.of.len (ULift.up i) =
        Sum.inr (ULift.up a) by rw [liftedFiniteSplit_apply, hq]; rfl]
    change a.val = i.val
    have hi := finSumFinEquiv.apply_symm_apply i
    rw [hq] at hi
    simpa only [finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.zero_add] using
      congrArg Fin.val hi

/-- The right source unitor deletes the actual empty finite block. -/
theorem smallEquivOfHom_rightUnitor (A : SmallFinBijGroupoid) :
    smallEquivOfHom (ρ_ A).hom = finCongr (Nat.add_zero A.of.len) := by
  let _ : IsEmpty (ULift.{0, 0} (Fin 0)) := ⟨fun z => Fin.elim0 z.down⟩
  let rightE := (liftedFiniteSplit A.of.len 0).trans (Equiv.sumEmpty _ _)
  have hRaw :
      (show ULift.{0, 0} (Fin (A.of.len + 0)) → ULift.{0, 0} (Fin A.of.len) from
        (ρ_ A).hom.iso.hom) = rightE := rfl
  apply Equiv.ext
  intro i
  change Fin (A.of.len + 0) at i
  apply Fin.ext
  change (((show ULift.{0, 0} (Fin (A.of.len + 0)) → ULift.{0, 0} (Fin A.of.len) from
    (ρ_ A).hom.iso.hom) (ULift.up i)).down).val = i.val
  rw [hRaw]
  dsimp only [rightE, Equiv.trans_apply]
  rcases hq : finSumFinEquiv.symm i with a | z
  · rw [show liftedFiniteSplit A.of.len 0 (ULift.up i) =
        Sum.inl (ULift.up a) by rw [liftedFiniteSplit_apply, hq]; rfl]
    change a.val = i.val
    have hi := finSumFinEquiv.apply_symm_apply i
    rw [hq] at hi
    simpa only [finSumFinEquiv_apply_left, Fin.val_castAdd] using congrArg Fin.val hi
  · exact Fin.elim0 z

/-- The source braiding is the original ordered finite block swap. -/
theorem smallEquivOfHom_braiding (A B : SmallFinBijGroupoid) :
    smallEquivOfHom (β_ A B).hom =
      (finAddFlip : Fin (A.of.len + B.of.len) ≃ Fin (B.of.len + A.of.len)) := by
  let braidE := (liftedFiniteSplit A.of.len B.of.len).trans
    ((Equiv.sumComm _ _).trans (liftedFiniteSplit B.of.len A.of.len).symm)
  have hRaw :
      (show ULift.{0, 0} (Fin (A.of.len + B.of.len)) →
          ULift.{0, 0} (Fin (B.of.len + A.of.len)) from
        (β_ A B).hom.iso.hom) = braidE := rfl
  apply Equiv.ext
  intro i
  change Fin (A.of.len + B.of.len) at i
  change ((show ULift.{0, 0} (Fin (A.of.len + B.of.len)) →
    ULift.{0, 0} (Fin (B.of.len + A.of.len)) from
    (β_ A B).hom.iso.hom) (ULift.up i)).down = finAddFlip i
  rw [hRaw]
  dsimp only [braidE, Equiv.trans_apply]
  rcases hq : finSumFinEquiv.symm i with a | b
  · have hi := finSumFinEquiv.apply_symm_apply i
    rw [hq] at hi
    subst i
    rw [show liftedFiniteSplit A.of.len B.of.len
      (ULift.up (finSumFinEquiv (Sum.inl a))) = Sum.inl (ULift.up a) by
        rw [liftedFiniteSplit_apply, Equiv.symm_apply_apply]; rfl]
    simp only [Equiv.sumComm_apply, Sum.swap_inl, finAddFlip_apply_castAdd,
      finSumFinEquiv_apply_left]
    change ((liftedFiniteSplit B.of.len A.of.len).symm
      (Sum.inr (ULift.up a))).down = Fin.natAdd B.of.len a
    exact congrArg ULift.down
      (liftedFiniteSplit_symm_apply B.of.len A.of.len (Sum.inr a))
  · have hi := finSumFinEquiv.apply_symm_apply i
    rw [hq] at hi
    subst i
    rw [show liftedFiniteSplit A.of.len B.of.len
      (ULift.up (finSumFinEquiv (Sum.inr b))) = Sum.inr (ULift.up b) by
        rw [liftedFiniteSplit_apply, Equiv.symm_apply_apply]; rfl]
    simp only [Equiv.sumComm_apply, Sum.swap_inr, finAddFlip_apply_natAdd,
      finSumFinEquiv_apply_right]
    change ((liftedFiniteSplit B.of.len A.of.len).symm
      (Sum.inl (ULift.up b))).down = Fin.castAdd A.of.len b
    exact congrArg ULift.down
      (liftedFiniteSplit_symm_apply B.of.len A.of.len (Sum.inl b))


/-- The ordered degree index enters the original finite-bijection groupoid by identity labels. -/
def degreeInclusion : N ⥤ I where
  obj a := card a.as.toAdd
  map f := (Discrete.functor (fun n : Multiplicative ℕ => card n.toAdd)).map f
  map_id a := (Discrete.functor (fun n : Multiplicative ℕ => card n.toAdd)).map_id a
  map_comp f g := (Discrete.functor (fun n : Multiplicative ℕ => card n.toAdd)).map_comp f g

/-- The directly stored degree data is the whole original discrete inclusion. -/
theorem degreeInclusion_original : degreeInclusion =
    Discrete.functor (fun n : Multiplicative ℕ => card n.toAdd) := rfl

/-- The literal finite degree is preserved by the ordered inclusion. -/
theorem degreeInclusion_obj (n : ℕ) :
    degreeInclusion.obj (CategoryTheory.Sequence.index n) = card n := rfl

/-- The degree equality carried by an original discrete index arrow. -/
theorem degreeArrowEquality {a b : N} (f : a ⟶ b) :
    CategoryTheory.Sequence.degree a = CategoryTheory.Sequence.degree b :=
  congrArg Multiplicative.toAdd (Discrete.eq_of_hom f)

/-- Every original ordered index arrow carries the same finite coordinate equality. -/
theorem degreeInclusion_map_finite {a b : N} (f : a ⟶ b) :
    smallEquivOfHom (degreeInclusion.map f) = finCongr (degreeArrowEquality f) := by
  have hab : a = b := Discrete.ext (Discrete.eq_of_hom f)
  subst b
  rw [show f = 𝟙 a from Discrete.hom_eq, degreeInclusion.map_id,
    smallEquivOfHom_id]
  rfl

/-- Equality of all original finite coordinates determines the complete index arrow. -/
theorem finiteArrow_ext {a b : I} {f g : a ⟶ b}
    (h : smallEquivOfHom f = smallEquivOfHom g) : f = g := by
  apply Core.hom_ext
  funext z
  rcases z with ⟨z⟩
  exact congrArg (fun e : Fin a.of.len ≃ Fin b.of.len => ULift.up (e z)) h

/-- The original ordered inclusion preserves the complete finite associator. -/
theorem degreeInclusion_associator (a b c : N) :
    degreeInclusion.map (α_ a b c).hom =
      (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom := by
  have hl : smallEquivOfHom (degreeInclusion.map (α_ a b c).hom) =
      finCongr (Nat.add_assoc (CategoryTheory.Sequence.degree a)
        (CategoryTheory.Sequence.degree b) (CategoryTheory.Sequence.degree c)) :=
    degreeInclusion_map_finite _
  have hr : smallEquivOfHom
      (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom =
      finCongr (Nat.add_assoc (CategoryTheory.Sequence.degree a)
        (CategoryTheory.Sequence.degree b) (CategoryTheory.Sequence.degree c)) :=
    smallEquivOfHom_associator _ _ _
  exact finiteArrow_ext (hl.trans hr.symm)

/-- The actual empty left finite block is preserved by the original ordered inclusion. -/
theorem degreeInclusion_leftUnitor (a : N) :
    degreeInclusion.map (λ_ a).hom = (λ_ (degreeInclusion.obj a)).hom := by
  have hl : smallEquivOfHom (degreeInclusion.map (λ_ a).hom) =
      finCongr (Nat.zero_add (CategoryTheory.Sequence.degree a)) := degreeInclusion_map_finite _
  have hr : smallEquivOfHom (λ_ (degreeInclusion.obj a)).hom =
      finCongr (Nat.zero_add (CategoryTheory.Sequence.degree a)) :=
    smallEquivOfHom_leftUnitor _
  exact finiteArrow_ext (hl.trans hr.symm)

/-- The actual empty right finite block is preserved by the original ordered inclusion. -/
theorem degreeInclusion_rightUnitor (a : N) :
    degreeInclusion.map (ρ_ a).hom = (ρ_ (degreeInclusion.obj a)).hom := by
  have hl : smallEquivOfHom (degreeInclusion.map (ρ_ a).hom) =
      finCongr (Nat.add_zero (CategoryTheory.Sequence.degree a)) := degreeInclusion_map_finite _
  have hr : smallEquivOfHom (ρ_ (degreeInclusion.obj a)).hom =
      finCongr (Nat.add_zero (CategoryTheory.Sequence.degree a)) :=
    smallEquivOfHom_rightUnitor _
  exact finiteArrow_ext (hl.trans hr.symm)

/-- The inverse original finite associator is also preserved on its complete coordinate map. -/
theorem degreeInclusion_associator_inv (a b c : N) :
    degreeInclusion.map (α_ a b c).inv =
      (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).inv := by
  have h : degreeInclusion.mapIso (α_ a b c) =
      α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c) :=
    Iso.ext (degreeInclusion_associator a b c)
  exact congrArg Iso.inv h

/-- The inverse original empty-left-block map retains the same full degree action. -/
theorem degreeInclusion_leftUnitor_inv (a : N) :
    degreeInclusion.map (λ_ a).inv = (λ_ (degreeInclusion.obj a)).inv := by
  have h : degreeInclusion.mapIso (λ_ a) = λ_ (degreeInclusion.obj a) :=
    Iso.ext (degreeInclusion_leftUnitor a)
  exact congrArg Iso.inv h

/-- The inverse original empty-right-block map retains the same full degree action. -/
theorem degreeInclusion_rightUnitor_inv (a : N) :
    degreeInclusion.map (ρ_ a).inv = (ρ_ (degreeInclusion.obj a)).inv := by
  have h : degreeInclusion.mapIso (ρ_ a) = ρ_ (degreeInclusion.obj a) :=
    Iso.ext (degreeInclusion_rightUnitor a)
  exact congrArg Iso.inv h

/-- The unit comparison is the original identity at degree zero. -/
def degreeUnitIso : 𝟙_ I ≅ degreeInclusion.obj (𝟙_ N) := Iso.refl (card 0)

/-- The tensor comparison is the original identity at the sum of the ordered degrees. -/
def degreeTensorIso (a b : N) :
    degreeInclusion.obj a ⊗ degreeInclusion.obj b ≅ degreeInclusion.obj (a ⊗ b) :=
  Iso.refl (card (CategoryTheory.Sequence.degree a + CategoryTheory.Sequence.degree b))

/-- The ordered finite-block inclusion is monoidal with its original identity tensorators. -/
def degreeInclusionCoreMonoidal : degreeInclusion.CoreMonoidal where
  εIso := degreeUnitIso
  μIso := degreeTensorIso
  μIso_hom_natural_left := by
    intro a b f c
    have hab : a = b := Discrete.ext (Discrete.eq_of_hom f)
    subst b
    have hf : f = 𝟙 a := Discrete.hom_eq
    cases hf
    have hl : degreeInclusion.map (𝟙 a) ▷ degreeInclusion.obj c ≫ (degreeTensorIso a c).hom =
        (degreeTensorIso a c).hom :=
      (congrArg (fun g : degreeInclusion.obj a ⟶ degreeInclusion.obj a =>
        (g ▷ degreeInclusion.obj c) ≫ (degreeTensorIso a c).hom) (degreeInclusion.map_id a)).trans
        ((congrArg (fun g => g ≫ (degreeTensorIso a c).hom)
          (MonoidalCategory.id_whiskerRight (degreeInclusion.obj a) (degreeInclusion.obj c))).trans
            (Category.id_comp _))
    have hr : (degreeTensorIso a c).hom ≫ degreeInclusion.map (𝟙 a ▷ c) =
        (degreeTensorIso a c).hom :=
      (congrArg (fun g : a ⊗ c ⟶ a ⊗ c => (degreeTensorIso a c).hom ≫ degreeInclusion.map g)
        (MonoidalCategory.id_whiskerRight a c)).trans
        ((congrArg (fun g => (degreeTensorIso a c).hom ≫ g)
          (degreeInclusion.map_id (a ⊗ c))).trans (Category.comp_id _))
    exact hl.trans hr.symm
  μIso_hom_natural_right := by
    intro a b c f
    have hab : a = b := Discrete.ext (Discrete.eq_of_hom f)
    subst b
    have hf : f = 𝟙 a := Discrete.hom_eq
    cases hf
    have hl : degreeInclusion.obj c ◁ degreeInclusion.map (𝟙 a) ≫ (degreeTensorIso c a).hom =
        (degreeTensorIso c a).hom :=
      (congrArg (fun g : degreeInclusion.obj a ⟶ degreeInclusion.obj a =>
        (degreeInclusion.obj c ◁ g) ≫ (degreeTensorIso c a).hom) (degreeInclusion.map_id a)).trans
        ((congrArg (fun g => g ≫ (degreeTensorIso c a).hom)
          (MonoidalCategory.whiskerLeft_id (degreeInclusion.obj c) (degreeInclusion.obj a))).trans
            (Category.id_comp _))
    have hr : (degreeTensorIso c a).hom ≫ degreeInclusion.map (c ◁ 𝟙 a) =
        (degreeTensorIso c a).hom :=
      (congrArg (fun g : c ⊗ a ⟶ c ⊗ a => (degreeTensorIso c a).hom ≫ degreeInclusion.map g)
        (MonoidalCategory.whiskerLeft_id c a)).trans
        ((congrArg (fun g => (degreeTensorIso c a).hom ≫ g)
          (degreeInclusion.map_id (c ⊗ a))).trans (Category.comp_id _))
    exact hl.trans hr.symm
  associativity := by
    intro a b c
    have hl : (degreeTensorIso a b).hom ▷ degreeInclusion.obj c ≫
        (degreeTensorIso (a ⊗ b) c).hom ≫ degreeInclusion.map (α_ a b c).hom =
        degreeInclusion.map (α_ a b c).hom :=
      (congrArg (fun g : degreeInclusion.obj (a ⊗ b) ⊗ degreeInclusion.obj c ⟶
          degreeInclusion.obj (a ⊗ b) ⊗ degreeInclusion.obj c =>
        g ≫ (degreeTensorIso (a ⊗ b) c).hom ≫ degreeInclusion.map (α_ a b c).hom)
        (MonoidalCategory.id_whiskerRight (degreeInclusion.obj (a ⊗ b))
          (degreeInclusion.obj c))).trans
          ((Category.id_comp _).trans (Category.id_comp _))
    have hr : (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom ≫
        (degreeInclusion.obj a ◁ (degreeTensorIso b c).hom) ≫
          (degreeTensorIso a (b ⊗ c)).hom =
        (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom :=
      (congrArg (fun g : degreeInclusion.obj a ⊗ degreeInclusion.obj (b ⊗ c) ⟶
          degreeInclusion.obj a ⊗ degreeInclusion.obj (b ⊗ c) =>
        (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom ≫
          g ≫ (degreeTensorIso a (b ⊗ c)).hom)
        (MonoidalCategory.whiskerLeft_id (degreeInclusion.obj a)
          (degreeInclusion.obj (b ⊗ c)))).trans
            ((congrArg (fun g =>
              (α_ (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c)).hom ≫ g)
              (Category.id_comp _)).trans (Category.comp_id _))
    exact hl.trans ((degreeInclusion_associator a b c).trans hr.symm)
  left_unitality := by
    intro a
    have h : degreeUnitIso.hom ▷ degreeInclusion.obj a ≫ (degreeTensorIso (𝟙_ N) a).hom ≫
        degreeInclusion.map (λ_ a).hom = degreeInclusion.map (λ_ a).hom :=
      (congrArg (fun g : (𝟙_ I) ⊗ degreeInclusion.obj a ⟶ (𝟙_ I) ⊗ degreeInclusion.obj a =>
        g ≫ (degreeTensorIso (𝟙_ N) a).hom ≫ degreeInclusion.map (λ_ a).hom)
        (MonoidalCategory.id_whiskerRight (𝟙_ I) (degreeInclusion.obj a))).trans
          ((Category.id_comp _).trans (Category.id_comp _))
    exact (degreeInclusion_leftUnitor a).symm.trans h.symm
  right_unitality := by
    intro a
    have h : degreeInclusion.obj a ◁ degreeUnitIso.hom ≫ (degreeTensorIso a (𝟙_ N)).hom ≫
        degreeInclusion.map (ρ_ a).hom = degreeInclusion.map (ρ_ a).hom :=
      (congrArg (fun g : degreeInclusion.obj a ⊗ (𝟙_ I) ⟶ degreeInclusion.obj a ⊗ (𝟙_ I) =>
        g ≫ (degreeTensorIso a (𝟙_ N)).hom ≫ degreeInclusion.map (ρ_ a).hom)
        (MonoidalCategory.whiskerLeft_id (degreeInclusion.obj a) (𝟙_ I))).trans
          ((Category.id_comp _).trans (Category.id_comp _))
    exact (degreeInclusion_rightUnitor a).symm.trans h.symm

/-- The actual ordered inclusion carries precisely its verified original strong monoidal
structure. -/
@[instance_reducible]
def degreeInclusionMonoidal : degreeInclusion.Monoidal := degreeInclusionCoreMonoidal.toMonoidal


end CategoryTheory.Operad.SmallFinBijGroupoid

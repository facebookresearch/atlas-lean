/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.HomologyZero
public import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Suspension

/-!
# Recursive coefficient-generic reduced sphere homology

Diagonal reduced computation `H̃ₙ(Sⁿ; R) ≅ R` in any abelian target
where singular homology has excision, defined recursively from the C2d
zero-sphere iso and the suspension iso.  The existing additive-group
fundamental class and coefficient-naturality API is retained below.

Off-diagonal reduced vanishing is proved by induction on `n`,
generalizing `k`, using totally-disconnected ordinary vanishing for
`S⁰` and the reduced suspension iso for the inductive step, together
with path-connected reduced `H₀` vanishing.

Ordinary diagonal `Hₙ(Sⁿ) ≅ R` for `n ≠ 0` and off-diagonal vanishing
for `k ≠ 0, k ≠ n` follow from the reduced statements via the
positive-degree reduced/ordinary comparison iso.  Positive-dimensional
`H₀(Sⁿ) ≅ R` is the augmentation iso.
-/

@[expose] public section

namespace AlgebraicTopology

open CategoryTheory Limits

universe w v u

/-- Recursive diagonal reduced sphere homology iso `H̃ₙ(Sⁿ; R) ≅ R`.

* `n = 0`: `sphereZeroReducedH0Iso R`.
* `n + 1`: the reduced suspension coordinate followed by the coordinate in degree `n`.

The excision argument is explicit so this applies both to additive groups and
to regular modules over an arbitrary commutative ring. -/
noncomputable def reducedSphereHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [HasCoproducts.{0} C] [AB4OfSize.{w} C]
    (R : C)
    [hExcisive : (singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] :
    (n : ℕ) → reducedSingularHomology.{w, v, u} C R n (TopCat.sphere.{w} n) ≅ R
  | 0 => sphereZeroReducedH0Iso.{w} (C := C) R
  | n + 1 =>
      reducedSphereSuspensionIso.{w, v, u} (C := C) R
          (hExcisive := hExcisive) n n ≪≫
        reducedSphereHomologyIso R n

/-- Canonical coefficient-object morphism `R ⟶ H̃ₙ(Sⁿ; R)` representing the
reduced fundamental class. For arbitrary additive-group coefficients the correct
generic object is this morphism from `R`, defined as the inverse of
`reducedSphereHomologyIso`. -/
noncomputable def reducedSphereFundamentalClassHom (R : AddCommGrpCat.{0}) (n : ℕ) :
    R ⟶ reducedSingularHomology AddCommGrpCat.{0} R n (TopCat.sphere.{0} n) :=
  (reducedSphereHomologyIso R n).inv

@[simp]
theorem reducedSphereHomologyIso_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [HasCoproducts.{0} C] [AB4OfSize.{w} C]
    (R : C)
    [hExcisive : (singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive] :
    reducedSphereHomologyIso.{w, v, u} (C := C) R
        (hExcisive := hExcisive) 0 = sphereZeroReducedH0Iso.{w} R :=
  rfl

/-- Recursive successor formula for the generalized sphere coordinate. -/
theorem reducedSphereHomologyIso_succ_of_excisive
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [HasCoproducts.{0} C] [AB4OfSize.{w} C]
    (R : C)
    [hExcisive : (singularHomologyIntData.{w, v, u} C R :
      TopPair.HomologyTheoryData.{w} C).IsExcisive]
    (n : ℕ) :
    reducedSphereHomologyIso.{w, v, u} (C := C) R
        (hExcisive := hExcisive) (n + 1) =
      reducedSphereSuspensionIso.{w, v, u} (C := C) R
          (hExcisive := hExcisive) n n ≪≫
        reducedSphereHomologyIso.{w, v, u} (C := C) R
          (hExcisive := hExcisive) n :=
  rfl

@[simp]
theorem reducedSphereHomologyIso_succ (R : AddCommGrpCat.{0}) (n : ℕ) :
    reducedSphereHomologyIso R (n + 1) =
      reducedSphereSuspensionIso R n n ≪≫ reducedSphereHomologyIso R n :=
  rfl

@[simp]
theorem reducedSphereFundamentalClassHom_zero (R : AddCommGrpCat.{0}) :
    reducedSphereFundamentalClassHom R 0 = (sphereZeroReducedH0Iso R).inv :=
  by simp [reducedSphereFundamentalClassHom]

theorem reducedSphereFundamentalClassHom_succ (R : AddCommGrpCat.{0}) (n : ℕ) :
    reducedSphereFundamentalClassHom R (n + 1) =
      reducedSphereFundamentalClassHom R n ≫ (reducedSphereSuspensionIso R n n).inv :=
  by simp [reducedSphereFundamentalClassHom, reducedSphereHomologyIso_succ]

@[reassoc (attr := simp), simp]
theorem reducedSphereFundamentalClassHom_comp_hom (R : AddCommGrpCat.{0}) (n : ℕ) :
    reducedSphereFundamentalClassHom R n ≫ (reducedSphereHomologyIso R n).hom = 𝟙 R := by
  simp [reducedSphereFundamentalClassHom]

/-- Recursive reduced sphere homology, natural in the coefficient object. -/
noncomputable def reducedSphereHomologyCoefficientNatIso :
    (n : ℕ) →
      reducedSingularHomologyCoefficientFunctor AddCommGrpCat.{0} n ⋙
          (evaluation TopCat.{0} AddCommGrpCat.{0}).obj
            (TopCat.sphere.{0} n) ≅
        (𝟭 AddCommGrpCat.{0} : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
  | 0 => sphereZeroReducedH0CoefficientNatIso
  | n + 1 =>
      reducedSphereSuspensionCoefficientNatIso n n ≪≫
        reducedSphereHomologyCoefficientNatIso n

@[simp]
theorem reducedSphereHomologyCoefficientNatIso_app
    (R : AddCommGrpCat.{0}) (n : ℕ) :
    (reducedSphereHomologyCoefficientNatIso n).app R =
      reducedSphereHomologyIso R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [reducedSphereHomologyIso_succ]
      change (reducedSphereSuspensionCoefficientNatIso n n).app R ≪≫
          (reducedSphereHomologyCoefficientNatIso n).app R =
        reducedSphereSuspensionIso R n n ≪≫ reducedSphereHomologyIso R n
      rw [ih]
      rfl

/-- The reduced fundamental class is natural in the coefficient object. -/
theorem reducedSphereFundamentalClassHom_naturality_coefficient
    {R S : AddCommGrpCat.{0}} (a : R ⟶ S) (n : ℕ) :
    a ≫ reducedSphereFundamentalClassHom S n =
      reducedSphereFundamentalClassHom R n ≫
        ((reducedSingularHomologyCoefficientFunctor AddCommGrpCat.{0} n).map a).app
          (TopCat.sphere.{0} n) := by
  change a ≫ (reducedSphereHomologyIso S n).inv =
    (reducedSphereHomologyIso R n).inv ≫ _
  rw [← reducedSphereHomologyCoefficientNatIso_app S n,
    ← reducedSphereHomologyCoefficientNatIso_app R n]
  exact (reducedSphereHomologyCoefficientNatIso n).inv.naturality a

/-! ## Reduced off-diagonal vanishing -/

theorem isZero_reducedSphereHomology_of_ne (R : AddCommGrpCat.{0}) (n k : ℕ) (hkn : k ≠ n) :
    IsZero (reducedSingularHomology AddCommGrpCat.{0} R k (TopCat.sphere.{0} n)) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd rfl hkn
    | succ j =>
      have hk : Nat.succ j ≠ 0 := Nat.succ_ne_zero j
      have hOrd : IsZero (((singularHomologyFunctor AddCommGrpCat.{0} (Nat.succ j)).obj R).obj
          (TopCat.sphere.{0} 0)) := by
        have : TotallyDisconnectedSpace ↥(TopCat.sphere.{0} 0) := inferInstance
        exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          AddCommGrpCat.{0} (Nat.succ j) R (TopCat.sphere.{0} 0) hk
      have iso : reducedSingularHomology AddCommGrpCat.{0} R (Nat.succ j) (TopCat.sphere.{0} 0) ≅
          ((singularHomologyFunctor AddCommGrpCat.{0} (Nat.succ j)).obj R).obj
            (TopCat.sphere.{0} 0) :=
        (reducedSingularHomologyFunctorIso AddCommGrpCat.{0} R (Nat.succ j) hk).app
          (TopCat.sphere.{0} 0)
      exact hOrd.of_iso iso
  | succ n ih =>
    cases k with
    | zero =>
      have : PathConnectedSpace ↥(TopCat.sphere.{0} (Nat.succ n)) :=
        pathConnectedSpace_sphere (Nat.succ n) (Nat.succ_ne_zero n)
      exact isZero_reducedSingularHomologyZero_of_pathConnectedSpace
        AddCommGrpCat.{0} R (TopCat.sphere.{0} (Nat.succ n))
    | succ j =>
      have hjn : j ≠ n := by
        intro heq
        exact hkn (congrArg Nat.succ heq)
      have ih_j : IsZero (reducedSingularHomology AddCommGrpCat.{0} R j (TopCat.sphere.{0} n)) :=
        ih j hjn
      exact ih_j.of_iso (reducedSphereSuspensionIso R n j)

/-- Reduced sphere homology vanishes off the diagonal, naturally in coefficients. -/
theorem isZero_reducedSphereHomologyCoefficientFunctor_of_ne
    (n k : ℕ) (hkn : k ≠ n) :
    IsZero
      (reducedSingularHomologyCoefficientFunctor AddCommGrpCat.{0} k ⋙
        (evaluation TopCat.{0} AddCommGrpCat.{0}).obj (TopCat.sphere.{0} n)) :=
  Functor.isZero _ (fun R => isZero_reducedSphereHomology_of_ne R n k hkn)

/-! ## Ordinary diagonal iso for `n ≠ 0` -/

/-- Ordinary homology of a positive-dimensional sphere in its dimension is the
coefficient object. -/
noncomputable def sphereHomologyDiagonalIso (R : AddCommGrpCat.{0}) (n : ℕ) (hn : n ≠ 0) :
    ((singularHomologyFunctor AddCommGrpCat.{0} n).obj R).obj (TopCat.sphere.{0} n) ≅ R :=
  ((reducedSingularHomologyFunctorIso AddCommGrpCat.{0} R n hn).app
      (TopCat.sphere.{0} n)).symm ≪≫ reducedSphereHomologyIso R n

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary diagonal sphere-homology identification in positive degree is
natural in the coefficient object. -/
theorem sphereHomologyDiagonalIso_hom_naturality_coefficient
    {R S : AddCommGrpCat.{0}} (a : R ⟶ S) (n : ℕ) (hn : n ≠ 0) :
    ((singularHomologyFunctor AddCommGrpCat.{0} n).map a).app
          (TopCat.sphere.{0} n) ≫
        (sphereHomologyDiagonalIso S n hn).hom =
      (sphereHomologyDiagonalIso R n hn).hom ≫ a := by
  let X := TopCat.sphere.{0} n
  let eR := (reducedSingularHomologyFunctorIso AddCommGrpCat.{0} R n hn).app X
  let eS := (reducedSingularHomologyFunctorIso AddCommGrpCat.{0} S n hn).app X
  let rα := (reducedSingularHomologyCoefficientMap AddCommGrpCat.{0} n a).app X
  let hα := ((singularHomologyFunctor AddCommGrpCat.{0} n).map a).app X
  have hcomparison : rα ≫ eS.hom = eR.hom ≫ hα := by
    dsimp [rα, eR, eS, hα, X]
    simpa only [NatTrans.comp_app, reducedSingularHomologyFunctorIso_hom] using
      congr_app (reducedSingularHomologyCoefficientMap_comp_ι
        AddCommGrpCat.{0} n a) (TopCat.sphere.{0} n)
  have hinv : hα ≫ eS.inv = eR.inv ≫ rα := by
    apply (cancel_epi eR.hom).mp
    rw [← Category.assoc, ← hcomparison]
    simp
  have hred : rα ≫ (reducedSphereHomologyIso S n).hom =
      (reducedSphereHomologyIso R n).hom ≫ a := by
    have h := (reducedSphereHomologyCoefficientNatIso n).hom.naturality a
    have hS : (reducedSphereHomologyCoefficientNatIso n).hom.app S =
        (reducedSphereHomologyIso S n).hom :=
      congrArg (fun e => e.hom) (reducedSphereHomologyCoefficientNatIso_app S n)
    have hR : (reducedSphereHomologyCoefficientNatIso n).hom.app R =
        (reducedSphereHomologyIso R n).hom :=
      congrArg (fun e => e.hom) (reducedSphereHomologyCoefficientNatIso_app R n)
    rw [hS, hR] at h
    simpa only [rα, X, Functor.comp_map, evaluation_obj_map, Functor.id_map,
      reducedSingularHomologyCoefficientFunctor, Functor.copyObj,
      reducedSingularHomologyCoefficientMap] using h
  change hα ≫ eS.inv ≫ (reducedSphereHomologyIso S n).hom =
    eR.inv ≫ (reducedSphereHomologyIso R n).hom ≫ a
  calc
    hα ≫ eS.inv ≫ (reducedSphereHomologyIso S n).hom =
        (hα ≫ eS.inv) ≫ (reducedSphereHomologyIso S n).hom := by simp
    _ = (eR.inv ≫ rα) ≫ (reducedSphereHomologyIso S n).hom := by rw [hinv]
    _ = eR.inv ≫ (rα ≫ (reducedSphereHomologyIso S n).hom) := by simp
    _ = eR.inv ≫ ((reducedSphereHomologyIso R n).hom ≫ a) := by rw [hred]
    _ = eR.inv ≫ (reducedSphereHomologyIso R n).hom ≫ a := by simp

/-- Ordinary diagonal sphere homology in positive degree, naturally in the
coefficient object. -/
noncomputable def sphereHomologyDiagonalCoefficientNatIso
    (n : ℕ) (hn : n ≠ 0) :
    singularHomologyFunctor AddCommGrpCat.{0} n ⋙
          (evaluation TopCat.{0} AddCommGrpCat.{0}).obj (TopCat.sphere.{0} n) ≅
      (𝟭 AddCommGrpCat.{0} : AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  NatIso.ofComponents
    (fun R => sphereHomologyDiagonalIso R n hn)
    (fun {_ _} a => sphereHomologyDiagonalIso_hom_naturality_coefficient a n hn)

@[simp]
theorem sphereHomologyDiagonalCoefficientNatIso_app
    (R : AddCommGrpCat.{0}) (n : ℕ) (hn : n ≠ 0) :
    (sphereHomologyDiagonalCoefficientNatIso n hn).app R =
      sphereHomologyDiagonalIso R n hn :=
  rfl

/-! ## Ordinary off-diagonal vanishing for `k ≠ 0` -/

theorem isZero_sphereHomology_of_ne (R : AddCommGrpCat.{0}) (n k : ℕ)
    (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{0} k).obj R).obj (TopCat.sphere.{0} n)) := by
  have hRed : IsZero (reducedSingularHomology AddCommGrpCat.{0} R k (TopCat.sphere.{0} n)) :=
    isZero_reducedSphereHomology_of_ne R n k hkn
  have iso : reducedSingularHomology AddCommGrpCat.{0} R k (TopCat.sphere.{0} n) ≅
      ((singularHomologyFunctor AddCommGrpCat.{0} k).obj R).obj (TopCat.sphere.{0} n) :=
    (reducedSingularHomologyFunctorIso AddCommGrpCat.{0} R k hk).app (TopCat.sphere.{0} n)
  exact hRed.of_iso iso.symm

/-- Away from degrees zero and the sphere dimension, sphere homology vanishes
naturally in coefficients. -/
theorem isZero_sphereHomologyCoefficientFunctor_of_ne
    (n k : ℕ) (hk : k ≠ 0) (hkn : k ≠ n) :
    IsZero
      (singularHomologyFunctor AddCommGrpCat.{0} k ⋙
        (evaluation TopCat.{0} AddCommGrpCat.{0}).obj (TopCat.sphere.{0} n)) :=
  Functor.isZero _ (fun R => isZero_sphereHomology_of_ne R n k hk hkn)

/-! ## Positive-dimensional `H₀` -/

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Degree-zero homology of a positive-dimensional sphere is the coefficient object. -/
noncomputable def spherePositiveH0Iso (R : C) (n : ℕ) (hn : n ≠ 0) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.sphere.{w} n) ≅ R := by
  haveI : PathConnectedSpace ↥(TopCat.sphere.{w} n) := pathConnectedSpace_sphere n hn
  exact asIso ((TopCat.sphere.{w} n).singularHomology₀ε R)

@[simp]
theorem spherePositiveH0Iso_hom (R : C) (n : ℕ) (hn : n ≠ 0) :
    (spherePositiveH0Iso R n hn).hom =
      (TopCat.sphere.{w} n).singularHomology₀ε R :=
  rfl

/-- Positive-dimensional degree-zero sphere homology is natural in the coefficient object. -/
theorem spherePositiveH0Iso_hom_naturality_coefficient
    {R S : C} (a : R ⟶ S) (n : ℕ) (hn : n ≠ 0) :
    ((singularHomologyFunctor C 0).map a).app (TopCat.sphere.{w} n) ≫
        (spherePositiveH0Iso S n hn).hom =
      (spherePositiveH0Iso R n hn).hom ≫ a := by
  simpa only [spherePositiveH0Iso_hom] using
    TopCat.singularHomology₀ε_naturality_coefficient
      (C := C) (TopCat.sphere.{w} n) a

/-- Positive-dimensional degree-zero sphere homology, naturally in coefficients. -/
noncomputable def spherePositiveH0CoefficientNatIso
    (n : ℕ) (hn : n ≠ 0) :
    singularHomologyFunctor C 0 ⋙
          (evaluation TopCat.{w} C).obj (TopCat.sphere.{w} n) ≅
      (𝟭 C : C ⥤ C) :=
  NatIso.ofComponents
    (fun R => spherePositiveH0Iso R n hn)
    (fun {_ _} a => spherePositiveH0Iso_hom_naturality_coefficient a n hn)

@[simp]
theorem spherePositiveH0CoefficientNatIso_app
    (R : C) (n : ℕ) (hn : n ≠ 0) :
    (spherePositiveH0CoefficientNatIso (C := C) n hn).app R =
      spherePositiveH0Iso R n hn :=
  rfl

end AlgebraicTopology

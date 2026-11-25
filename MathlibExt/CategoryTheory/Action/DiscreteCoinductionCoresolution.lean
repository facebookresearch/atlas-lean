/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionMonad
public import MathlibExt.CategoryTheory.Monad.Coresolution
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# The original continuous coinduction monad and its coresolution

Transport the actual forget/coinduction adjunction along the original untwist.
The underlying functor remains the existing continuous coinduction, the unit
is its existing constant inclusion, and multiplication evaluates both function
coordinates at the same group element. Monad powers retain the original
continuous homogeneous-resolution coefficients and their stored modules.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w v₀ u₀
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The stock representation/action equivalence retains the exact original coinduction
coefficient. -/
def coindToTopRepIso (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.obj (coind.{u, w}.obj A) ≅ (toTopRep.obj A).coind₁ :=
  TopRep.toActionFromAction ((toTopRep.obj A).coind₁)

/-- The original coefficient conversion retains every coinduced function value. -/
theorem coindToTopRepIso_hom_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (z : underlying (coind.{u, w}.obj A)) (g : G) :
    ((coindToTopRepIso.{u, w} G A).hom.hom z) g = coindFunction.{u, w} A z g := rfl

/-- The original coefficient conversion has the literal inverse function values. -/
theorem coindToTopRepIso_inv_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (z : (toTopRep.obj A).coind₁) (g : G) :
    coindFunction.{u, w} A ((coindToTopRepIso.{u, w} G A).inv.hom z) g = z g := rfl

/-- The original coinduction comparison preserves every actual coefficient arrow. -/
theorem coindToTopRepIso_naturality {A B : DiscreteAbelianAction.{u, max u w} G}
    (f : A ⟶ B) :
    toTopRep.map (coind.{u, w}.map f) ≫ (coindToTopRepIso.{u, w} G B).hom =
      (coindToTopRepIso.{u, w} G A).hom ≫ (TopRep.coind₁Functor ℤ G).map (toTopRep.map f) := by
  rfl

/-- The actual monad unit becomes the stock constant inclusion in the original representation. -/
theorem coindToTopRepIso_unit (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((coindMonad.{u, w} G).η.app A) ≫ (coindToTopRepIso.{u, w} G A).hom =
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (toTopRep.obj A) := by
  have h := congrArg (fun f : A ⟶ coind.{u, w}.obj A =>
    toTopRep.map f ≫ (coindToTopRepIso.{u, w} G A).hom) (coindMonad_unit.{u, w} G A)
  exact h.trans (by rfl)

/-- The original nested resolution coface inserts a constant coordinate at its specified
position. -/
def coindResolutionCoface (X : TopRep.{max u w, 0, u} ℤ G) :
    (n : ℕ) → Fin (n + 1) → (TopRep.resolutionX X n ⟶ TopRep.resolutionX X (n + 1))
  | 0, _ => (TopRep.coind₁ι (k := ℤ) (G := G)).app X
  | n + 1, ⟨0, _⟩ =>
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX X (n + 1))
  | n + 1, ⟨i + 1, hi⟩ =>
      (TopRep.coind₁Functor ℤ G).map
        (coindResolutionCoface X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The first original coface is the stock constant-coordinate inclusion. -/
theorem coindResolutionCoface_zero (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    coindResolutionCoface.{u, w} G X n 0 =
      (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX X n) := by
  cases n <;> rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Successive original cofaces are the actual coinduced preceding operators. -/
theorem coindResolutionCoface_succ (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ)
    (i : Fin (n + 1)) :
    coindResolutionCoface.{u, w} G X (n + 1) i.succ =
      (TopRep.coind₁Functor ℤ G).map (coindResolutionCoface.{u, w} G X n i) := rfl

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The alternating original cofaces give exactly the stock continuous-resolution differential. -/
theorem coindResolutionCoface_sum (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • coindResolutionCoface.{u, w} G X n i) =
      TopRep.d X n := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, pow_zero, one_zsmul, coindResolutionCoface, TopRep.d_zero]
      rfl
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_zsmul,
        coindResolutionCoface_zero, coindResolutionCoface_succ]
      rw [TopRep.d_succ, ← ih, Functor.map_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
      exact congrArg (fun f => -f)
        (Functor.map_smul (TopRep.coind₁Functor ℤ G) ((-1 : ℤ) ^ i.val)
          (coindResolutionCoface.{u, w} G X n i)).symm

private theorem barEtaZeroInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (A : C) :
    Monad.barEtaAtPos T n 0 A ≫ eqToHom (Monad.monadPow_succ_obj_eq T n A) =
      T.η.app ((Monad.monadPow T n).obj A) := by
  simp only [Monad.barEtaAtPos, Fin.rev_zero]
  induction n generalizing A with
  | zero => exact Category.comp_id _
  | succ n ih => exact ih (T.obj A)

private theorem etaCastSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.etaAtPos T (n + 1) i.castSucc A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T n A) ≫ T.map (Monad.etaAtPos T n i A) := by
  induction n generalizing A with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact Monad.monadPow_obj_T_comm_naturality T 0 (T.η.app A)
  | succ n ih =>
      cases i with
      | mk val hval =>
          cases val with
          | zero =>
              exact Monad.monadPow_obj_T_comm_naturality T (n + 1) (T.η.app A)
          | succ k =>
              exact ih ⟨k, Nat.lt_of_succ_lt_succ hval⟩ (T.obj A)

private theorem barEtaSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.barEtaAtPos T (n + 1) i.succ A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T n A) ≫ T.map (Monad.barEtaAtPos T n i A) := by
  simp only [Monad.barEtaAtPos, Fin.rev_succ]
  exact etaCastSuccInPowers T n i.rev A

/-- Monad powers have the original nested continuous-resolution coefficients. -/
def coindPowerToTopRepIso (A : DiscreteAbelianAction.{u, max u w} G) :
    (n : ℕ) → toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≅
      TopRep.resolutionX (toTopRep.obj A) n
  | 0 => Iso.refl (toTopRep.obj A)
  | n + 1 =>
      toTopRep.mapIso (eqToIso (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≪≫
      coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≪≫
      (TopRep.coind₁Functor ℤ G).mapIso (coindPowerToTopRepIso A n)

/-- The actual degree object of the canonical coresolution is the original shifted resolution
term. -/
def coindCoresolutionTermIso (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.obj ((Monad.coresolution (coindMonad.{u, w} G) A).obj (SimplexCategory.mk n)) ≅
      TopRep.resolution'X (toTopRep.obj A) n :=
  toTopRep.mapIso (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n) ≪≫
    coindPowerToTopRepIso.{u, w} G A (n + 1)

/-- The successor comparison uses the actual power commutation and original coinduction
comparison. -/
theorem coindPowerToTopRepIso_succ_hom (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
      (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom ≫
      (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := rfl

private theorem threeSquareComposite {C : Type u₀} [Category.{v₀} C]
    {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : C}
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁) (d : D₀ ⟶ D₁)
    (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁)
    (f₀ : B₀ ⟶ C₀) (f₁ : B₁ ⟶ C₁)
    (g₀ : C₀ ⟶ D₀) (g₁ : C₁ ⟶ D₁)
    (ha : a ≫ e₁ = e₀ ≫ b) (hb : b ≫ f₁ = f₀ ≫ c) (hc : c ≫ g₁ = g₀ ≫ d) :
    a ≫ (e₁ ≫ f₁ ≫ g₁) = (e₀ ≫ f₀ ≫ g₀) ≫ d := by
  calc
    a ≫ (e₁ ≫ f₁ ≫ g₁) = (a ≫ e₁) ≫ f₁ ≫ g₁ := (Category.assoc _ _ _).symm
    _ = (e₀ ≫ b) ≫ f₁ ≫ g₁ := congrArg (fun f => f ≫ f₁ ≫ g₁) ha
    _ = e₀ ≫ (b ≫ f₁) ≫ g₁ := by simp only [Category.assoc]
    _ = e₀ ≫ (f₀ ≫ c) ≫ g₁ := congrArg (fun f => e₀ ≫ f ≫ g₁) hb
    _ = e₀ ≫ f₀ ≫ (c ≫ g₁) := by simp only [Category.assoc]
    _ = e₀ ≫ f₀ ≫ (g₀ ≫ d) := congrArg (fun f => e₀ ≫ f₀ ≫ f) hc
    _ = (e₀ ≫ f₀ ≫ g₀) ≫ d := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The outer original unit insertion becomes the native constant coface in every degree. -/
theorem coindPowerToTopRepIso_coface_zero (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A n).hom ≫
        (TopRep.coind₁ι (k := ℤ) (G := G)).app (TopRep.resolutionX (toTopRep.obj A) n) := by
  rw [coindPowerToTopRepIso_succ_hom]
  have hp := (Functor.map_comp toTopRep (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A)
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))).symm.trans
      (congrArg (fun f => toTopRep.map f) (barEtaZeroInPowers (coindMonad.{u, w} G) n A))
  have hu := coindToTopRepIso_unit.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
  calc
    _ = ((toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n 0 A) ≫
        toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))) ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := by
      simp only [Category.assoc]
    _ = (toTopRep.map ((coindMonad.{u, w} G).η.app
          ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
      congrArg (fun f => (f ≫
        (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom) hp
    _ = (TopRep.coind₁ι (k := ℤ) (G := G)).app
          (toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
      congrArg (fun f => f ≫
        (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom) hu
    _ = _ := ((TopRep.coind₁ι (k := ℤ) (G := G)).naturality
      (coindPowerToTopRepIso.{u, w} G A n).hom).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual monad unit insertion becomes the corresponding original continuous coface. -/
theorem coindPowerToTopRepIso_coface (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) n i A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A n).hom ≫
        coindResolutionCoface.{u, w} G (toTopRep.obj A) n i := by
  induction n with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      simpa only [coindResolutionCoface_zero] using coindPowerToTopRepIso_coface_zero.{u, w} G A 0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [coindResolutionCoface_zero] using
          coindPowerToTopRepIso_coface_zero.{u, w} G A (n + 1)
      · let φ := Monad.barEtaAtPos (coindMonad.{u, w} G) n j A
        have hp := (Functor.map_comp toTopRep
          (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) j.succ A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))).symm.trans
            ((congrArg (fun f => toTopRep.map f)
              (barEtaSuccInPowers (coindMonad.{u, w} G) n j A)).trans
                (Functor.map_comp toTopRep
                  (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
                  ((coindMonad.{u, w} G).map φ)))
        have hj := coindToTopRepIso_naturality.{u, w} G φ
        have hh := (Functor.map_comp (TopRep.coind₁Functor ℤ G) (toTopRep.map φ)
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom).symm.trans
            ((congrArg (fun f => (TopRep.coind₁Functor ℤ G).map f) (ih j)).trans
              (Functor.map_comp (TopRep.coind₁Functor ℤ G)
                (coindPowerToTopRepIso.{u, w} G A n).hom
                (coindResolutionCoface.{u, w} G (toTopRep.obj A) n j)))
        rw [coindPowerToTopRepIso_succ_hom G A (n + 1),
          coindPowerToTopRepIso_succ_hom G A n, coindResolutionCoface_succ]
        exact threeSquareComposite
          (toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) j.succ A))
          (toTopRep.map ((coindMonad.{u, w} G).map φ))
          ((TopRep.coind₁Functor ℤ G).map (toTopRep.map φ))
          ((TopRep.coind₁Functor ℤ G).map (coindResolutionCoface.{u, w} G (toTopRep.obj A) n j))
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)))
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A)))
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)).hom
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom)
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom)
          hp hj hh

/-- The actual degree comparison first uses the canonical monad-power coordinates. -/
theorem coindCoresolutionTermIso_hom (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    (coindCoresolutionTermIso.{u, w} G A n).hom =
      toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual canonical coresolution coface is the original native continuous coface. -/
theorem coindCoresolution_coface (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 2)) :
    toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i)) ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫
        coindResolutionCoface.{u, w} G (toTopRep.obj A) (n + 1) i := by
  rw [coindCoresolutionTermIso_hom, coindCoresolutionTermIso_hom]
  have hc := (Functor.map_comp toTopRep
    ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i))
    (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom).symm.trans
      ((congrArg (fun f => toTopRep.map f)
        (Monad.coresolutionObjIso_coface (coindMonad.{u, w} G) A i)).trans
          (Functor.map_comp toTopRep (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom
            (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A)))
  have hp := coindPowerToTopRepIso_coface.{u, w} G A (n + 1) i
  calc
    _ = (toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.δ i)) ≫
        toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom := (Category.assoc _ _ _).symm
    _ = (toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A)) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom :=
      congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom) hc
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        (toTopRep.map (Monad.barEtaAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 2)).hom) := Category.assoc _ _ _
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        ((coindPowerToTopRepIso.{u, w} G A (n + 1)).hom ≫
          coindResolutionCoface.{u, w} G (toTopRep.obj A) (n + 1) i) :=
      congrArg (fun f => toTopRep.map
        (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫ f) hp
    _ = _ := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical alternating differential is exactly the original shifted continuous
differential. -/
theorem coindCoresolution_differential (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) n ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫ TopRep.d (toTopRep.obj A) (n + 1) := by
  rw [← coindResolutionCoface_sum.{u, w} G (toTopRep.obj A) (n + 1), Preadditive.comp_sum]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD,
    Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f :
    toTopRep.obj ((Monad.coresolution (coindMonad.{u, w} G) A).obj (SimplexCategory.mk n)) ⟶
      TopRep.resolutionX (toTopRep.obj A) (n + 2) => (-1 : ℤ) ^ i.val • f)
    (coindCoresolution_coface.{u, w} G A n i)

private theorem alternatingComplexSuccessor {C : Type u₀} [Category.{v₀} C]
    [Preadditive C] (X : CosimplicialObject C) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X n := by
  dsimp only [AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj]
  exact CochainComplex.of_d (fun i => X.obj (SimplexCategory.mk i))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD X) n

set_option backward.isDefEq.respectTransparency.types false in
/-- The exact differentials of the two original full complexes commute with the degree
comparison. -/
theorem coindCoresolution_complex_differential (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep)).d n (n + 1) ≫
        (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫
        (TopRep.resolution' (toTopRep.obj A)).d n (n + 1) := by
  have hs := alternatingComplexSuccessor
    ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) n
  have ht : (TopRep.resolution' (toTopRep.obj A)).d n (n + 1) =
      TopRep.d (toTopRep.obj A) (n + 1) := CochainComplex.of_d _ _ n
  exact (congrArg (fun f => f ≫ (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom) hs).trans
    ((coindCoresolution_differential.{u, w} G A n).trans
      (congrArg (fun f => (coindCoresolutionTermIso.{u, w} G A n).hom ≫ f) ht.symm))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical coinduction coresolution computes the original shifted native
resolution. -/
def coindCoresolutionComplexIso (A : DiscreteAbelianAction.{u, max u w} G) :
    (AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
        ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep) ≅
      TopRep.resolution' (toTopRep.obj A) :=
  HomologicalComplex.Hom.isoOfComponents
    (C₁ := (AlgebraicTopology.alternatingCofaceMapComplex (TopRep.{max u w, 0, u} ℤ G)).obj
      ((Monad.coresolution (coindMonad.{u, w} G) A) ⋙ toTopRep))
    (C₂ := TopRep.resolution' (toTopRep.obj A))
    (coindCoresolutionTermIso.{u, w} G A)
    (fun i j hij => by
      change i + 1 = j at hij
      subst j
      exact (coindCoresolution_complex_differential.{u, w} G A i).symm)

omit [TotallyDisconnectedSpace G] in
/-- The actual native diagonal evaluates both continuous coordinates at the same group element. -/
def coindResolutionDiagonal (X : TopRep.{max u w, 0, u} ℤ G) : X.coind₁.coind₁ ⟶ X.coind₁ := by
  letI : Module ℤ X := X.hV2
  letI : Module ℤ X.coind₁ := X.coind₁.hV2
  letI : Module ℤ X.coind₁.coind₁ := X.coind₁.coind₁.hV2
  let δ : C(G, G × G) := ⟨fun g => (g, g), continuous_id.prodMk continuous_id⟩
  exact TopRep.ofHom
    { toFun := fun z => (ContinuousMap.uncurry z).comp δ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun _ => rfl
      cont := (ContinuousMap.continuous_precomp δ).comp ContinuousMap.continuous_uncurry }

omit [TotallyDisconnectedSpace G] in
/-- The diagonal is the literal original two-coordinate evaluator on every native vector. -/
theorem coindResolutionDiagonal_apply (X : TopRep.{max u w, 0, u} ℤ G)
    (z : X.coind₁.coind₁) (g : G) :
    ((coindResolutionDiagonal.{u, w} G X).hom z) g = z g g := rfl

omit [TotallyDisconnectedSpace G] in
/-- The native diagonal commutes with every actual continuous coefficient arrow. -/
theorem coindResolutionDiagonal_naturality {X Y : TopRep.{max u w, 0, u} ℤ G}
    (f : X ⟶ Y) :
    (TopRep.coind₁Functor ℤ G).map ((TopRep.coind₁Functor ℤ G).map f) ≫
        coindResolutionDiagonal.{u, w} G Y =
      coindResolutionDiagonal.{u, w} G X ≫ (TopRep.coind₁Functor ℤ G).map f := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual transported multiplication is the original native diagonal, not a new coefficient
map. -/
theorem coindToTopRepIso_mul (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((coindMonad.{u, w} G).μ.app A) ≫ (coindToTopRepIso.{u, w} G A).hom =
      (coindToTopRepIso.{u, w} G (coind.{u, w}.obj A)).hom ≫
        (TopRep.coind₁Functor ℤ G).map (coindToTopRepIso.{u, w} G A).hom ≫
        coindResolutionDiagonal.{u, w} G (toTopRep.obj A) := by
  let : Module ℤ (toTopRep.obj
      (((coindMonad.{u, w} G).toFunctor ⋙ (coindMonad.{u, w} G).toFunctor).obj A)) :=
    (toTopRep.obj
      (((coindMonad.{u, w} G).toFunctor ⋙ (coindMonad.{u, w} G).toFunctor).obj A)).hV2
  let : Module ℤ (toTopRep.obj A).coind₁ := (toTopRep.obj A).coind₁.hV2
  apply TopRep.hom_ext
  refine ContIntertwiningMap.ext ?_
  refine ContinuousLinearMap.ext (fun z => ?_)
  refine ContinuousMap.ext (fun g => ?_)
  exact coindMonad_mul_apply.{u, w} G A z g

omit [TotallyDisconnectedSpace G] in
/-- Original native codegeneracies repeat the selected adjacent function coordinates. -/
def coindResolutionCodegeneracy (X : TopRep.{max u w, 0, u} ℤ G) :
    (n : ℕ) → Fin n → (TopRep.resolutionX X (n + 1) ⟶ TopRep.resolutionX X n)
  | 0, i => Fin.elim0 i
  | n + 1, ⟨0, _⟩ => coindResolutionDiagonal.{u, w} G (TopRep.resolutionX X n)
  | n + 1, ⟨i + 1, hi⟩ =>
      (TopRep.coind₁Functor ℤ G).map
        (coindResolutionCodegeneracy X n ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

omit [TotallyDisconnectedSpace G] in
/-- The first original codegeneracy is the literal outer diagonal. -/
theorem coindResolutionCodegeneracy_zero (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ) :
    coindResolutionCodegeneracy.{u, w} G X (n + 1) 0 =
      coindResolutionDiagonal.{u, w} G (TopRep.resolutionX X n) := rfl

omit [TotallyDisconnectedSpace G] in
/-- Every later native codegeneracy is the actual coinduced preceding diagonal operator. -/
theorem coindResolutionCodegeneracy_succ (X : TopRep.{max u w, 0, u} ℤ G) (n : ℕ)
    (i : Fin (n + 1)) :
    coindResolutionCodegeneracy.{u, w} G X (n + 2) i.succ =
      (TopRep.coind₁Functor ℤ G).map (coindResolutionCodegeneracy.{u, w} G X (n + 1) i) := rfl

private theorem barMuZeroInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (A : C) :
    Monad.barMuAtPos T (n + 1) 0 A ≫ eqToHom (Monad.monadPow_succ_obj_eq T n A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) ≫
        T.map (eqToHom (Monad.monadPow_succ_obj_eq T n A)) ≫
        T.μ.app ((Monad.monadPow T n).obj A) := by
  simp only [Monad.barMuAtPos, Fin.rev_zero]
  induction n generalizing A with
  | zero =>
      change T.μ.app A ≫ 𝟙 _ = 𝟙 _ ≫ T.map (𝟙 (T.obj A)) ≫ T.μ.app A
      rw [Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
  | succ n ih => exact ih (T.obj A)

private theorem muCastSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.muAtPos T (n + 2) i.castSucc A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 2) A) ≫
        T.map (Monad.muAtPos T (n + 1) i A) := by
  induction n generalizing A with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      exact Monad.monadPow_obj_T_comm_naturality T 0 (T.μ.app A)
  | succ n ih =>
      cases i with
      | mk val hval =>
          cases val with
          | zero => exact Monad.monadPow_obj_T_comm_naturality T (n + 1) (T.μ.app A)
          | succ k => exact ih ⟨k, Nat.lt_of_succ_lt_succ hval⟩ (T.obj A)

private theorem barMuSuccInPowers {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (A : C) :
    Monad.barMuAtPos T (n + 2) i.succ A ≫
        eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A) =
      eqToHom (Monad.monadPow_succ_obj_eq T (n + 2) A) ≫
        T.map (Monad.barMuAtPos T (n + 1) i A) := by
  simp only [Monad.barMuAtPos, Fin.rev_succ]
  exact muCastSuccInPowers T n i.rev A

private def mapIntoDoubleSource {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (P Q : C) (e : Q ⟶ T.obj P) :
    L.obj (T.obj Q) ⟶ L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) := L.map (T.map e)

private theorem mapIntoDoubleSource_eq {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (P Q : C) (e : Q ⟶ T.obj P) :
    mapIntoDoubleSource T L P Q e = L.map (T.map e) := rfl

private theorem mappedBarMuZero {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D) (n : ℕ) (A : C) :
    L.map (Monad.barMuAtPos T (n + 1) 0 A) ≫
        L.map (eqToHom (Monad.monadPow_succ_obj_eq T n A)) =
      L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫
        CategoryStruct.comp
          (Y := L.obj ((T.toFunctor ⋙ T.toFunctor).obj ((Monad.monadPow T n).obj A)))
          (mapIntoDoubleSource T L ((Monad.monadPow T n).obj A)
            ((Monad.monadPow T (n + 1)).obj A)
            (eqToHom (Monad.monadPow_succ_obj_eq T n A)))
          (L.map (T.μ.app ((Monad.monadPow T n).obj A))) := by
  exact ((Functor.map_comp L _ _).symm.trans
    ((congrArg (fun f => L.map f) (barMuZeroInPowers T n A)).trans
      ((Functor.map_comp L _ _).trans
        (congrArg (fun f => L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫ f)
          (Functor.map_comp L _ _))))).trans
    (congrArg (fun b => L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) ≫
        b ≫ L.map (T.μ.app ((Monad.monadPow T n).obj A)))
      (mapIntoDoubleSource_eq T L ((Monad.monadPow T n).obj A)
        ((Monad.monadPow T (n + 1)).obj A)
        (eqToHom (Monad.monadPow_succ_obj_eq T n A))).symm)

private theorem mappedBarMuSucc {C : Type u₀} [Category.{v₀} C]
    {D : Type u} [Category.{w} D] (T : Monad C) (L : C ⥤ D)
    (n : ℕ) (i : Fin (n + 1)) (A : C) :
    L.map (Monad.barMuAtPos T (n + 1 + 1) i.succ A) ≫
        L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1) A)) =
      L.map (eqToHom (Monad.monadPow_succ_obj_eq T (n + 1 + 1) A)) ≫
        L.map (T.map (Monad.barMuAtPos T (n + 1) i A)) := by
  exact (Functor.map_comp L _ _).symm.trans
    ((congrArg (fun f => L.map f) (barMuSuccInPowers T n i A)).trans
      (Functor.map_comp L _ _))

private theorem diagonalFunctorComposite {C : Type u₀} [Category.{v₀} C]
    (F : C ⥤ C) {P Q Q' BP BQ BBP N : C}
    (m : Q' ⟶ Q) (E₀ : Q ⟶ BP) (E₁ : Q' ⟶ BQ)
    (B : BQ ⟶ BBP) (M : BBP ⟶ BP)
    (J₀ : BP ⟶ F.obj P) (J₁ : BQ ⟶ F.obj Q) (J₂ : BBP ⟶ F.obj BP)
    (I₀ : P ⟶ N) (D₀ : F.obj (F.obj P) ⟶ F.obj P)
    (D₁ : F.obj (F.obj N) ⟶ F.obj N)
    (hp : m ≫ E₀ = E₁ ≫ B ≫ M)
    (hu : M ≫ J₀ = J₂ ≫ F.map J₀ ≫ D₀)
    (hj : B ≫ J₂ = J₁ ≫ F.map E₀)
    (hd : D₀ ≫ F.map I₀ = F.map (F.map I₀) ≫ D₁) :
    m ≫ (E₀ ≫ J₀ ≫ F.map I₀) = (E₁ ≫ J₁ ≫ F.map (E₀ ≫ J₀ ≫ F.map I₀)) ≫ D₁ := by
  calc
    _ = ((m ≫ E₀) ≫ J₀) ≫ F.map I₀ := by simp only [Category.assoc]
    _ = ((E₁ ≫ B ≫ M) ≫ J₀) ≫ F.map I₀ := congrArg (fun f => (f ≫ J₀) ≫ F.map I₀) hp
    _ = E₁ ≫ B ≫ (M ≫ J₀) ≫ F.map I₀ := by simp only [Category.assoc]
    _ = E₁ ≫ B ≫ (J₂ ≫ F.map J₀ ≫ D₀) ≫ F.map I₀ :=
      congrArg (fun f => E₁ ≫ B ≫ f ≫ F.map I₀) hu
    _ = E₁ ≫ (B ≫ J₂) ≫ F.map J₀ ≫ D₀ ≫ F.map I₀ := by simp only [Category.assoc]
    _ = E₁ ≫ (J₁ ≫ F.map E₀) ≫ F.map J₀ ≫ D₀ ≫ F.map I₀ :=
      congrArg (fun f => E₁ ≫ f ≫ F.map J₀ ≫ D₀ ≫ F.map I₀) hj
    _ = E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ (D₀ ≫ F.map I₀) := by simp only [Category.assoc]
    _ = E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ (F.map (F.map I₀) ≫ D₁) :=
      congrArg (fun f => E₁ ≫ J₁ ≫ F.map E₀ ≫ F.map J₀ ≫ f) hd
    _ = (E₁ ≫ J₁ ≫ (F.map E₀ ≫ F.map J₀ ≫ F.map (F.map I₀))) ≫ D₁ := by
      simp only [Category.assoc]
    _ = _ := congrArg (fun f => (E₁ ≫ J₁ ≫ f) ≫ D₁)
      ((Functor.map_comp F E₀ (J₀ ≫ F.map I₀)).trans
        (congrArg (fun f => F.map E₀ ≫ f) (Functor.map_comp F J₀ (F.map I₀)))).symm

private theorem diagonalFunctionComposite {ι : Type u₀}
    {P Q Q' BP BQ BBP N : Type v₀}
    (m : Q' → Q) (E₀ : Q → BP) (E₁ : Q' → BQ) (B : BQ → BBP) (M : BBP → BP)
    (J₀ : BP → ι → P) (J₁ : BQ → ι → Q) (J₂ : BBP → ι → BP) (I₀ : P → N)
    (hp : ∀ x, E₀ (m x) = M (B (E₁ x)))
    (hu : ∀ y i, J₀ (M y) i = J₀ (J₂ y i) i)
    (hj : ∀ y i, J₂ (B y) i = E₀ (J₁ y i)) (x : Q') (i : ι) :
    I₀ (J₀ (E₀ (m x)) i) = I₀ (J₀ (E₀ (J₁ (E₁ x) i)) i) :=
  (congrArg (fun y => I₀ (J₀ y i)) (hp x)).trans
    ((congrArg I₀ (hu (B (E₁ x)) i)).trans
      (congrArg (fun y => I₀ (J₀ y i)) (hj (E₁ x) i)))

private theorem transferExpandedSquare {C : Type u₀} [Category.{v₀} C]
    {R Q X Y : C} (m : R ⟶ Q) (l l₀ : Q ⟶ X) (r r₀ : R ⟶ Y) (d : Y ⟶ X)
    (h : m ≫ l₀ = r₀ ≫ d) (hl : l = l₀) (hr : r = r₀) : m ≫ l = r ≫ d :=
  (congrArg (fun f => m ≫ f) hl).trans (h.trans (congrArg (fun f => f ≫ d) hr.symm))

private theorem transferSquareTarget {C : Type u₀} [Category.{v₀} C]
    {R Q X Y : C} (m : R ⟶ Q) (l l₀ : Q ⟶ X) (r r₀ : R ⟶ Y) (d d₀ : Y ⟶ X)
    (h : m ≫ l₀ = r₀ ≫ d₀) (hl : l = l₀) (hr : r = r₀) (hd : d = d₀) :
    m ≫ l = r ≫ d :=
  (transferExpandedSquare m l l₀ r r₀ d₀ h hl hr).trans
    (congrArg (fun f => r ≫ f) hd.symm)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem topRepTwoThreeValueEq {A₀ A₁ A₂ A₃ A₄ : TopRep.{max u w, 0, u} ℤ G}
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₄) (h : A₀ ⟶ A₂)
    (i : A₂ ⟶ A₃) (j : A₃ ⟶ A₄) (heq : f ≫ g = h ≫ i ≫ j) (x : A₀) :
    g.hom (f.hom x) = j.hom (i.hom (h.hom x)) :=
  congrArg (fun k : A₀ ⟶ A₄ => k.hom x) heq

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem topRepTwoTwoValueEq {A₀ A₁ A₂ A₃ : TopRep.{max u w, 0, u} ℤ G}
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₃) (h : A₀ ⟶ A₂)
    (i : A₂ ⟶ A₃) (heq : f ≫ g = h ≫ i) (x : A₀) :
    g.hom (f.hom x) = i.hom (h.hom x) :=
  congrArg (fun k : A₀ ⟶ A₃ => k.hom x) heq

private def coindMonadToTopRepHom (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.obj ((coindMonad.{u, w} G).obj A) ⟶
      (TopRep.coind₁Functor ℤ G).obj (toTopRep.obj A) := by
  change toTopRep.obj (coind.{u, w}.obj A) ⟶ (toTopRep.obj A).coind₁
  exact (coindToTopRepIso.{u, w} G A).hom

private theorem coindMonadToTopRepHom_eq (A : DiscreteAbelianAction.{u, max u w} G) :
    coindMonadToTopRepHom.{u, w} G A = (coindToTopRepIso.{u, w} G A).hom := by
  rfl

private theorem coindMappedBarMuZero (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A) ≫
        toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A)) ≫
        mapIntoDoubleSource (coindMonad.{u, w} G) (toTopRep.{u, max u w} (G := G))
          ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
            toTopRep.map ((coindMonad.{u, w} G).μ.app
              ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)) := by
  with_reducible exact (mappedBarMuZero (coindMonad.{u, w} G)
    (toTopRep.{u, max u w} (G := G)) n A)

private theorem coindDiagonalTypedSquare
    (P Q R : DiscreteAbelianAction.{u, max u w} G)
    (N : TopRep.{max u w, 0, u} ℤ G)
    (m : R ⟶ Q)
    (e₀ : Q ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : R ⟶ (coindMonad.{u, w} G).obj Q)
    (I₀ : toTopRep.obj P ⟶ N)
    (hp :
      toTopRep.map m ≫ toTopRep.map e₀ =
        toTopRep.map e₁ ≫
          mapIntoDoubleSource (coindMonad.{u, w} G)
            (toTopRep.{u, max u w} (G := G)) P Q e₀ ≫
          toTopRep.map ((coindMonad.{u, w} G).μ.app P)) :
    toTopRep.map m ≫
        (toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
          (TopRep.coind₁Functor ℤ G).map I₀) =
      (toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
        (TopRep.coind₁Functor ℤ G).map
          (toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
            (TopRep.coind₁Functor ℤ G).map I₀)) ≫
        coindResolutionDiagonal.{u, w} G N := by
  let T : Monad (DiscreteAbelianAction.{u, max u w} G) := coindMonad.{u, w} G
  let L : DiscreteAbelianAction.{u, max u w} G ⥤ TopRep.{max u w, 0, u} ℤ G :=
    toTopRep.{u, max u w} (G := G)
  let F : TopRep.{max u w, 0, u} ℤ G ⥤ TopRep.{max u w, 0, u} ℤ G :=
    TopRep.coind₁Functor ℤ G
  let m₀ : L.obj R ⟶ L.obj Q := L.map m
  let E₀ : L.obj Q ⟶ L.obj (T.obj P) := L.map e₀
  let E₁ : L.obj R ⟶ L.obj (T.obj Q) := L.map e₁
  let B : L.obj (T.obj Q) ⟶ L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) :=
    mapIntoDoubleSource T L P Q e₀
  let M : L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) ⟶ L.obj (T.obj P) :=
    L.map (T.μ.app P)
  let J₀ : L.obj (T.obj P) ⟶ F.obj (L.obj P) := coindMonadToTopRepHom.{u, w} G P
  let J₁ : L.obj (T.obj Q) ⟶ F.obj (L.obj Q) := coindMonadToTopRepHom.{u, w} G Q
  let J₂ : L.obj ((T.toFunctor ⋙ T.toFunctor).obj P) ⟶ F.obj (L.obj (T.obj P)) := by
    change L.obj (T.obj (T.obj P)) ⟶ F.obj (L.obj (T.obj P))
    exact coindMonadToTopRepHom.{u, w} G (T.obj P)
  let D₀ : F.obj (F.obj (L.obj P)) ⟶ F.obj (L.obj P) :=
    coindResolutionDiagonal.{u, w} G (L.obj P)
  let D₁ : F.obj (F.obj N) ⟶ F.obj N := coindResolutionDiagonal.{u, w} G N
  have hu : M ≫ J₀ = J₂ ≫ F.map J₀ ≫ D₀ := coindToTopRepIso_mul.{u, w} G P
  have hj : B ≫ J₂ = J₁ ≫ F.map E₀ := coindToTopRepIso_naturality.{u, w} G e₀
  have hd : D₀ ≫ F.map I₀ = F.map (F.map I₀) ≫ D₁ :=
    (coindResolutionDiagonal_naturality.{u, w} G I₀).symm
  exact diagonalFunctorComposite
    (C := TopRep.{max u w, 0, u} ℤ G) F
    (P := L.obj P) (Q := L.obj Q) (Q' := L.obj R)
    (BP := L.obj (T.obj P)) (BQ := L.obj (T.obj Q))
    (BBP := L.obj ((T.toFunctor ⋙ T.toFunctor).obj P)) (N := N)
    m₀ E₀ E₁ B M J₀ J₁ J₂ I₀ D₀ D₁ hp hu hj hd


private theorem coindDiagonalFullTypedSquare
    (P Q R : DiscreteAbelianAction.{u, max u w} G)
    (N : TopRep.{max u w, 0, u} ℤ G)
    (m : R ⟶ Q)
    (e₀ : Q ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : R ⟶ (coindMonad.{u, w} G).obj Q)
    (I₀ : toTopRep.obj P ⟶ N)
    (I₁ : toTopRep.obj Q ⟶ (TopRep.coind₁Functor ℤ G).obj N)
    (I₂ : toTopRep.obj R ⟶ (TopRep.coind₁Functor ℤ G).obj ((TopRep.coind₁Functor ℤ G).obj N))
    (hp :
      toTopRep.map m ≫ toTopRep.map e₀ =
        toTopRep.map e₁ ≫
          mapIntoDoubleSource (coindMonad.{u, w} G)
            (toTopRep.{u, max u w} (G := G)) P Q e₀ ≫
          toTopRep.map ((coindMonad.{u, w} G).μ.app P))
    (h₀ : I₁ = toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
      (TopRep.coind₁Functor ℤ G).map I₀)
    (h₁ : I₂ = toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
      (TopRep.coind₁Functor ℤ G).map I₁) :
    toTopRep.map m ≫ I₁ = I₂ ≫ coindResolutionDiagonal.{u, w} G N := by
  let L := toTopRep.{u, max u w} (G := G)
  let F := TopRep.coind₁Functor ℤ G
  let l₀ := L.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫ F.map I₀
  let r₀ := L.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫ F.map l₀
  have h := coindDiagonalTypedSquare.{u, w} G P Q R N m e₀ e₁ I₀ hp
  have hr : I₂ = r₀ := h₁.trans
    (congrArg (fun f : L.obj Q ⟶ F.obj N =>
      (show L.obj R ⟶ F.obj (F.obj N) from L.map e₁ ≫
        coindMonadToTopRepHom.{u, w} G Q ≫ F.map f)) h₀)
  exact transferExpandedSquare (L.map m) I₁ l₀ I₂ r₀
    (coindResolutionDiagonal.{u, w} G N) h h₀ hr

private def coindPowerSuccNativeHom (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A) ⟶
      (TopRep.coind₁Functor ℤ G).obj (TopRep.resolutionX (toTopRep.obj A) n) :=
  (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom

private theorem coindPowerSuccNativeHom_eq (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    coindPowerSuccNativeHom.{u, w} G A n =
      (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := rfl

private theorem coindPowerSuccHomNormalized (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
        coindMonadToTopRepHom.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≫
          (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom := by
  let L := toTopRep.{u, max u w} (G := G)
  let E := L.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
  let F := TopRep.coind₁Functor ℤ G
  let I := (coindPowerToTopRepIso.{u, w} G A n).hom
  exact (coindPowerToTopRepIso_succ_hom.{u, w} G A n).trans
    (congrArg (fun j => E ≫ j ≫ F.map I)
      (coindMonadToTopRepHom_eq.{u, w} G
        ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).symm)

private theorem coindPowerSuccNativeHom_normalized
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    coindPowerSuccNativeHom.{u, w} G A n =
      toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
        coindMonadToTopRepHom.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A) ≫
          (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom :=
  (coindPowerSuccNativeHom_eq.{u, w} G A n).trans
    (coindPowerSuccHomNormalized.{u, w} G A n)

private theorem coindMapFullTypedSquare
    (P Q R S : DiscreteAbelianAction.{u, max u w} G)
    (NP NQ : TopRep.{max u w, 0, u} ℤ G) (φ : P ⟶ Q) (m : R ⟶ S)
    (e₀ : R ⟶ (coindMonad.{u, w} G).obj P)
    (e₁ : S ⟶ (coindMonad.{u, w} G).obj Q)
    (IP : toTopRep.obj P ⟶ NP) (IQ : toTopRep.obj Q ⟶ NQ)
    (IR : toTopRep.obj R ⟶ (TopRep.coind₁Functor ℤ G).obj NP)
    (IS : toTopRep.obj S ⟶ (TopRep.coind₁Functor ℤ G).obj NQ) (d : NP ⟶ NQ)
    (hp : toTopRep.map m ≫ toTopRep.map e₁ =
      toTopRep.map e₀ ≫ toTopRep.map ((coindMonad.{u, w} G).map φ))
    (hI : toTopRep.map φ ≫ IQ = IP ≫ d)
    (hR : IR = toTopRep.map e₀ ≫ coindMonadToTopRepHom.{u, w} G P ≫
      (TopRep.coind₁Functor ℤ G).map IP)
    (hS : IS = toTopRep.map e₁ ≫ coindMonadToTopRepHom.{u, w} G Q ≫
      (TopRep.coind₁Functor ℤ G).map IQ) :
    toTopRep.map m ≫ IS = IR ≫ (TopRep.coind₁Functor ℤ G).map d := by
  let L := toTopRep.{u, max u w} (G := G)
  let F := TopRep.coind₁Functor ℤ G
  let J₀ := coindMonadToTopRepHom.{u, w} G P
  let J₁ := coindMonadToTopRepHom.{u, w} G Q
  have hj : L.map ((coindMonad.{u, w} G).map φ) ≫ J₁ = J₀ ≫ F.map (L.map φ) :=
    coindToTopRepIso_naturality.{u, w} G φ
  have hh : F.map (L.map φ) ≫ F.map IQ = F.map IP ≫ F.map d :=
    (Functor.map_comp F (L.map φ) IQ).symm.trans
      ((congrArg (fun f => F.map f) hI).trans (Functor.map_comp F IP d))
  have he := threeSquareComposite (L.map m) (L.map ((coindMonad.{u, w} G).map φ))
    (F.map (L.map φ)) (F.map d) (L.map e₀) (L.map e₁) J₀ J₁
    (F.map IP) (F.map IQ) hp hj hh
  exact transferExpandedSquare (L.map m) IS (L.map e₁ ≫ J₁ ≫ F.map IQ)
    IR (L.map e₀ ≫ J₀ ≫ F.map IP) (F.map d) he hS hR

set_option backward.isDefEq.respectTransparency.types true in
/-- The outer original multiplication insertion becomes the literal native diagonal in every
degree. -/
theorem coindPowerToTopRepIso_codegeneracy_zero
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
        coindResolutionDiagonal.{u, w} G (TopRep.resolutionX (toTopRep.obj A) n) := by
  exact coindDiagonalFullTypedSquare.{u, w} G
    ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)
    ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
    ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
    (TopRep.resolutionX (toTopRep.obj A) n)
    (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) 0 A)
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A))
    (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))
    (coindPowerToTopRepIso.{u, w} G A n).hom
    (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom
    (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
    (coindMappedBarMuZero.{u, w} G A n)
    (coindPowerSuccHomNormalized.{u, w} G A n)
    (coindPowerSuccHomNormalized.{u, w} G A (n + 1))

set_option backward.isDefEq.respectTransparency.types true in
/-- Every actual source-ordered multiplication insertion becomes its original native
codegeneracy. -/
theorem coindPowerToTopRepIso_codegeneracy
    (A : DiscreteAbelianAction.{u, max u w} G) (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
        (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom =
      (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
        coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i := by
  induction n with
  | zero =>
      have hi : i = 0 := by apply Fin.ext; omega
      subst i
      simpa only [coindResolutionCodegeneracy_zero] using
        coindPowerToTopRepIso_codegeneracy_zero.{u, w} G A 0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [coindResolutionCodegeneracy_zero] using
          coindPowerToTopRepIso_codegeneracy_zero.{u, w} G A (n + 1)
      · let φ := Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) j A
        have h := coindMapFullTypedSquare.{u, w} G
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1 + 1)).obj A)
          ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A)
          (TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1))
          (TopRep.resolutionX (toTopRep.obj A) (n + 1)) φ
          (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1 + 1) j.succ A)
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1 + 1) A))
          (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) (n + 1) A))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1 + 1))
          (coindPowerSuccNativeHom.{u, w} G A (n + 1))
          (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) j)
          (mappedBarMuSucc (coindMonad.{u, w} G) (toTopRep.{u, max u w} (G := G)) n j A) (ih j)
          (by with_reducible exact (coindPowerSuccNativeHom_normalized.{u, w} G A (n + 1 + 1)))
          (by with_reducible exact (coindPowerSuccNativeHom_normalized.{u, w} G A (n + 1)))
        have hResult := transferSquareTarget (C := TopRep.{max u w, 0, u} ℤ G)
          (R := toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1 + 1)).obj A))
          (Q := toTopRep.obj ((Monad.monadPow (coindMonad.{u, w} G) (n + 1 + 1)).obj A))
          (X := TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1))
          (Y := TopRep.resolutionX (toTopRep.obj A) (n + 1 + 1 + 1))
          (toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1 + 1) j.succ A))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1))
          (coindPowerToTopRepIso.{u, w} G A (n + 1 + 1 + 1)).hom
          (coindPowerSuccNativeHom.{u, w} G A (n + 1 + 1))
          (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1 + 1) j.succ)
          ((TopRep.coind₁Functor ℤ G).map
            (coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) j))
          (by with_reducible exact h)
          (by with_reducible exact (coindPowerSuccNativeHom_eq.{u, w} G A (n + 1)).symm)
          (by with_reducible exact (coindPowerSuccNativeHom_eq.{u, w} G A (n + 1 + 1)).symm)
          (by with_reducible exact (coindResolutionCodegeneracy_succ.{u, w} G (toTopRep.obj A) n j))
        exact hResult

set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual canonical coresolution codegeneracy repeats the corresponding original native
coordinate. -/
theorem coindCoresolution_codegeneracy (A : DiscreteAbelianAction.{u, max u w} G)
    (n : ℕ) (i : Fin (n + 1)) :
    toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i)) ≫
        (coindCoresolutionTermIso.{u, w} G A n).hom =
      (coindCoresolutionTermIso.{u, w} G A (n + 1)).hom ≫
        coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i := by
  rw [coindCoresolutionTermIso_hom, coindCoresolutionTermIso_hom]
  have hc := (Functor.map_comp toTopRep
    ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i))
    (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom).symm.trans
      ((congrArg (fun f => toTopRep.map f)
        (Monad.coresolutionObjIso_codegeneracy (coindMonad.{u, w} G) A i)).trans
          (Functor.map_comp toTopRep (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom
            (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A)))
  have hp := coindPowerToTopRepIso_codegeneracy.{u, w} G A n i
  calc
    _ = (toTopRep.map ((Monad.coresolution (coindMonad.{u, w} G) A).map (SimplexCategory.σ i)) ≫
        toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom := (Category.assoc _ _ _).symm
    _ = (toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A)) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom :=
      congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom) hc
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        (toTopRep.map (Monad.barMuAtPos (coindMonad.{u, w} G) (n + 1) i A) ≫
          (coindPowerToTopRepIso.{u, w} G A (n + 1)).hom) := Category.assoc _ _ _
    _ = toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫
        ((coindPowerToTopRepIso.{u, w} G A (n + 1 + 1)).hom ≫
          coindResolutionCodegeneracy.{u, w} G (toTopRep.obj A) (n + 1) i) :=
      congrArg (fun f => toTopRep.map
        (Monad.coresolutionObjIso (coindMonad.{u, w} G) A (n + 1)).hom ≫ f) hp
    _ = _ := (Category.assoc _ _ _).symm

private theorem coresolutionZeroCoordinates {C : Type u₀} [Category.{v₀} C]
    (T : Monad C) (A : C) :
    (Monad.coresolutionObjIso T A 0).hom = 𝟙 (T.obj A) := by
  rw [Monad.coresolutionObjIso_hom]
  rfl

private theorem coindPowerOneHom (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindPowerToTopRepIso.{u, w} G A 1).hom = (coindToTopRepIso.{u, w} G A).hom := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual degree-zero comparison retains the original native coinduction coordinates. -/
theorem coindCoresolutionTermIso_zero_hom (A : DiscreteAbelianAction.{u, max u w} G) :
    (coindCoresolutionTermIso.{u, w} G A 0).hom = (coindToTopRepIso.{u, w} G A).hom := by
  let L := toTopRep.{u, max u w} (G := G)
  rw [coindCoresolutionTermIso_hom]
  have hc := (congrArg (fun f => L.map f)
    (coresolutionZeroCoordinates (coindMonad.{u, w} G) A)).trans
      (Functor.map_id L ((coindMonad.{u, w} G).obj A))
  exact (congrArg (fun f => f ≫ (coindPowerToTopRepIso.{u, w} G A 1).hom) hc).trans
    ((Category.id_comp _).trans (coindPowerOneHom.{u, w} G A))

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical coaugmentation is the original continuous constant inclusion. -/
theorem coindCoresolution_coaugmentation (A : DiscreteAbelianAction.{u, max u w} G) :
    toTopRep.map ((Monad.coresolutionAugmented (coindMonad.{u, w} G) A).hom.app
      (SimplexCategory.mk 0)) ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom =
        (TopRep.coind₁ι (k := ℤ) (G := G)).app (toTopRep.obj A) := by
  let L := toTopRep.{u, max u w} (G := G)
  have ha := congrArg (fun f => L.map f)
    (Monad.coresolutionAugmented_hom_zero (coindMonad.{u, w} G) A)
  have ht := coindCoresolutionTermIso_zero_hom.{u, w} G A
  exact (congrArg (fun f => f ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom) ha).trans
    ((congrArg (fun f => L.map ((coindMonad.{u, w} G).η.app A) ≫ f) ht).trans
      (coindToTopRepIso_unit.{u, w} G A))

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original coaugmentation vector has the same value at every group element. -/
theorem coindCoresolution_coaugmentation_apply (A : DiscreteAbelianAction.{u, max u w} G)
    (a : underlying A) (g : G) :
    ((toTopRep.map ((Monad.coresolutionAugmented (coindMonad.{u, w} G) A).hom.app
      (SimplexCategory.mk 0)) ≫ (coindCoresolutionTermIso.{u, w} G A 0).hom).hom a) g = a := by
  have h := congrArg (fun f : toTopRep.obj A ⟶ (toTopRep.obj A).coind₁ => f.hom a g)
    (coindCoresolution_coaugmentation.{u, w} G A)
  exact h.trans rfl

end CategoryTheory.DiscreteAbelianAction

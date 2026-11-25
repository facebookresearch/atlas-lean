/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Finite-tuple evaluation of continuous homogeneous resolutions

The continuous homogeneous resolution represents an `n`-variable cochain by
an iterated compact-open continuous-map carrier.  This file evaluates that
nested carrier on a tuple indexed by `Fin n`.  Evaluation is injective,
respects subtraction and the diagonal action, and turns the recursively
defined differential into the usual alternating coordinate-deletion sum.

Joint continuity of evaluation uses local compactness of the group.  The
algebraic formulas do not.

## Main declarations

* `ContinuousCohomology.resolutionFinUncurry`
* `ContinuousCohomology.resolutionFinUncurry_resolutionMap`
* `ContinuousCohomology.continuous_resolutionFinUncurry`
* `ContinuousCohomology.resolutionFinUncurry_injective`
* `ContinuousCohomology.resolutionFinUncurry_action`
* `ContinuousCohomology.resolutionFinUncurry_d`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory ContRepresentation

universe u v w

namespace ContinuousCohomology

variable {k : Type u} {G : Type v}
variable [Ring k] [TopologicalSpace k]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluate the nested compact-open carrier of the continuous homogeneous
resolution on one finite tuple. -/
def resolutionFinUncurry (X : TopRep.{max v w, u, v} k G) :
    (n : ℕ) → TopRep.resolutionX X n → (Fin n → G) → X
  | 0, a, _ => a
  | n + 1, f, x => resolutionFinUncurry X n (f (x 0)) (Fin.tail x)

/-- Evaluation on the empty tuple returns the coefficient. -/
@[simp]
theorem resolutionFinUncurry_zero (X : TopRep.{max v w, u, v} k G)
    (a : X) (x : Fin 0 → G) :
    resolutionFinUncurry X 0 a x = a := rfl

/-- Evaluation on a nonempty tuple first evaluates at its head. -/
@[simp]
theorem resolutionFinUncurry_succ (X : TopRep.{max v w, u, v} k G)
    (n : ℕ) (f : TopRep.resolutionX X (n + 1))
    (x : Fin (n + 1) → G) :
    resolutionFinUncurry X (n + 1) f x =
      resolutionFinUncurry X n (f (x 0)) (Fin.tail x) := rfl

/-- Finite-tuple evaluation is natural under the resolution map induced by
a continuous group homomorphism and an equivariant coefficient map. -/
theorem resolutionFinUncurry_resolutionMap
    {H : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X : TopRep.{max v w, u, v} k G}
    {Y : TopRep.{max v w, u, v} k H}
    (phi : H →ₜ* G) (f : TopRep.res phi X ⟶ Y) :
    ∀ (n : ℕ) (c : TopRep.resolutionX X n) (x : Fin n → H),
      resolutionFinUncurry Y n ((resolutionMap phi f n).hom c) x =
        f.hom (resolutionFinUncurry X n c (fun i => phi (x i)))
  | 0, c, x => rfl
  | n + 1, c, x => by
      change resolutionFinUncurry Y n
          ((resolutionMap phi f n).hom (c (phi (x 0)))) (Fin.tail x) = _
      rw [resolutionFinUncurry_resolutionMap]
      rfl

/-- Joint continuity of finite-tuple evaluation. -/
theorem continuous_resolutionFinUncurry [LocallyCompactSpace G]
    (X : TopRep.{max v w, u, v} k G) :
    ∀ n : ℕ, Continuous (fun p : TopRep.resolutionX X n × (Fin n → G) =>
      resolutionFinUncurry X n p.1 p.2)
  | 0 => continuous_fst
  | n + 1 => by
      change Continuous (fun p :
        TopRep.resolutionX X (n + 1) × (Fin (n + 1) → G) =>
          resolutionFinUncurry X n (p.1 (p.2 0)) (Fin.tail p.2))
      exact (continuous_resolutionFinUncurry X n).comp
        ((continuous_fst.eval ((continuous_apply 0).comp continuous_snd)).prodMk
          continuous_snd.finTail)

/-- A fixed nested resolution element evaluates continuously on finite
tuples. -/
theorem continuous_resolutionFinUncurry_left
    (X : TopRep.{max v w, u, v} k G) [LocallyCompactSpace G]
    (n : ℕ) (f : TopRep.resolutionX X n) :
    Continuous (resolutionFinUncurry X n f) :=
  (continuous_resolutionFinUncurry X n).comp
    (continuous_const.prodMk continuous_id)

/-- Evaluation on all finite tuples determines a nested resolution element. -/
theorem resolutionFinUncurry_injective
    (X : TopRep.{max v w, u, v} k G) :
    ∀ n : ℕ, Function.Injective (resolutionFinUncurry X n)
  | 0, f, g, h => congrFun h Fin.elim0
  | n + 1, f, g, h => by
      apply ContinuousMap.ext
      intro x
      apply resolutionFinUncurry_injective X n
      funext y
      exact congrFun h (Fin.cons x y)

/-- Finite-tuple evaluation respects subtraction. -/
@[simp]
theorem resolutionFinUncurry_sub (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (f g : TopRep.resolutionX X n),
      resolutionFinUncurry X n (f - g) =
        resolutionFinUncurry X n f - resolutionFinUncurry X n g
  | 0, f, g => rfl
  | n + 1, f, g => by
      funext x
      change resolutionFinUncurry X n (f (x 0) - g (x 0)) (Fin.tail x) = _
      rw [resolutionFinUncurry_sub]
      rfl

/-- Evaluation of the diagonal action on an iterated continuous function. -/
theorem resolutionFinUncurry_action (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (g : G) (f : TopRep.resolutionX X n) (x : Fin n → G),
      resolutionFinUncurry X n ((TopRep.resolutionX X n).ρ g f) x =
        X.ρ g (resolutionFinUncurry X n f (fun i => g⁻¹ * x i))
  | 0, g, f, x => rfl
  | n + 1, g, f, x => by
      change resolutionFinUncurry X n
        ((TopRep.resolutionX X n).ρ g (f (g⁻¹ * x 0))) (Fin.tail x) = _
      rw [resolutionFinUncurry_action]
      rfl

/-- Evaluation of the homogeneous differential is the alternating sum over
coordinate deletions, with the `j`-th term obtained using `j.succAbove`. -/
theorem resolutionFinUncurry_d (X : TopRep.{max v w, u, v} k G) :
    ∀ (n : ℕ) (f : TopRep.resolution'X X n) (x : Fin (n + 2) → G),
      resolutionFinUncurry X (n + 2) ((TopRep.d X (n + 1)).hom f) x =
        ∑ j : Fin (n + 2), (-1 : k) ^ (j : ℕ) •
          resolutionFinUncurry X (n + 1) f (fun i => x (j.succAbove i))
  | 0, f, x => by
      rw [TopRep.hom_d_succ]
      change f (x 1) - f (x 0) = _
      rw [Fin.sum_univ_two]
      simp only [resolutionFinUncurry]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        Fin.zero_succAbove, Fin.one_succAbove_zero]
      change f (x 1) - f (x 0) = (1 : k) • f (x 1) + (-1 : k) • f (x 0)
      rw [one_smul k, neg_one_smul k, sub_eq_add_neg]
  | n + 1, f, x => by
      rw [TopRep.hom_d_succ]
      simp only [ContIntertwiningMap.sub_apply,
        ContRepresentation.coind₁ι_toFun,
        ContRepresentation.coind₁Map_toFun]
      rw [resolutionFinUncurry_sub]
      change resolutionFinUncurry X (n + 2) f (Fin.tail x) -
          resolutionFinUncurry X (n + 2)
            ((TopRep.d X (n + 1)).hom (f (x 0))) (Fin.tail x) = _
      rw [resolutionFinUncurry_d]
      have hhead :
          (-1 : k) ^ ((0 : Fin (n + 3)) : ℕ) •
              resolutionFinUncurry X (n + 2) f
                (fun i => x ((0 : Fin (n + 3)).succAbove i)) =
            resolutionFinUncurry X (n + 2) f (Fin.tail x) := by
        simp
        congr 1
      have hterm (j : Fin (n + 2)) :
          resolutionFinUncurry X (n + 2) f
              (fun i => x (j.succ.succAbove i)) =
            resolutionFinUncurry X (n + 1) (f (x 0))
              (fun i => Fin.tail x (j.succAbove i)) := by
        change resolutionFinUncurry X (n + 1)
            (f (x (j.succ.succAbove 0)))
            (Fin.tail (fun i => x (j.succ.succAbove i))) = _
        congr 1
        funext i
        exact congrArg x (Fin.succ_succAbove_succ j i)
      have hsum :
          -(∑ j : Fin (n + 2), (-1 : k) ^ (j : ℕ) •
              resolutionFinUncurry X (n + 1) (f (x 0))
                (fun i => Fin.tail x (j.succAbove i))) =
            ∑ j : Fin (n + 2), (-1 : k) ^ (j.succ : ℕ) •
              resolutionFinUncurry X (n + 2) f
                (fun i => x (j.succ.succAbove i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [hterm]
        simp [pow_succ]
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [hhead, ← hsum]
      exact sub_eq_add_neg _ _

end ContinuousCohomology

end

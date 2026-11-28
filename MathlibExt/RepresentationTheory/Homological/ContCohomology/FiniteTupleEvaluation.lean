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
# Finite-tuple evaluation of iterated continuous coefficients

Let k be a ring with a topology, G a topological group and X a
topological k-representation. Put U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)).
Evaluation recursively takes the first group coordinate, then the remaining
tuple. It is injective, respects subtraction and the diagonal action,
and gives the alternating deletion formula for the homogeneous differential.

These algebraic value formulas do not require local compactness.
When G is locally compact, evaluation is jointly continuous in the
nested coefficient and finite tuple. Scalar, group and carrier universes
are independent.
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
The finite-tuple evaluator E_n : U_n(X) → (G^n → X) is
E₀(a)=a and E_(n+1)(F)(t)=E_n(F(t₀))(tail(t)). -/
def resolutionFinUncurry (X : TopRep.{max v w, u, v} k G) :
    (n : ℕ) → TopRep.resolutionX X n → (Fin n → G) → X
  | 0, a, _ => a
  | n + 1, f, x => resolutionFinUncurry X n (f (x 0)) (Fin.tail x)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
For a ∈ X and the unique empty tuple t, E₀(a)(t)=a. -/
@[simp]
theorem resolutionFinUncurry_zero (X : TopRep.{max v w, u, v} k G)
    (a : X) (x : Fin 0 → G) :
    resolutionFinUncurry X 0 a x = a := rfl

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
For F ∈ U_(n+1)(X), evaluation on a nonempty tuple is
E_(n+1)(F)(t)=E_n(F(t₀))(tail(t)). -/
@[simp]
theorem resolutionFinUncurry_succ (X : TopRep.{max v w, u, v} k G)
    (n : ℕ) (f : TopRep.resolutionX X (n + 1))
    (x : Fin (n + 1) → G) :
    resolutionFinUncurry X (n + 1) f x =
      resolutionFinUncurry X n (f (x 0)) (Fin.tail x) := rfl

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Let H be a topological group in the same group universe,
φ : H → G continuous, and f : Res_φ(X) → Y a continuous equivariant
k-linear map. The induced resolution map satisfies
E_n^Y(resolutionMap(c))(t)=f(E_n^X(c)(φ(t₀),…,φ(t_(n-1)))). -/
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
For every n ∈ ℕ, (c,t) ↦ E_n(c)(t) is jointly continuous
on U_n(X) × G^n. -/
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Assume G is locally compact.
For fixed c ∈ U_n(X), the function t ↦ E_n(c)(t) on G^n
is continuous. -/
theorem continuous_resolutionFinUncurry_left
    (X : TopRep.{max v w, u, v} k G) [LocallyCompactSpace G]
    (n : ℕ) (f : TopRep.resolutionX X n) :
    Continuous (resolutionFinUncurry X n f) :=
  (continuous_resolutionFinUncurry X n).comp
    (continuous_const.prodMk continuous_id)

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
The map c ↦ E_n(c) is injective for every n ∈ ℕ:
equality on all finite tuples implies equality in U_n(X). -/
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
Finite-tuple evaluation respects subtraction:
E_n(c-c′)=E_n(c)-E_n(c′) pointwise. -/
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
The diagonal G-action has evaluation formula
E_n(g • c)(t)=g • E_n(c)(g⁻¹t₀,…,g⁻¹t_(n-1)). -/
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

/-- Let k be a ring with a topology and G a topological group.
Let X be a topological k-module with a G-representation by continuous
k-linear maps, with carrier universe max(v,w), independently of the
scalar universe u and group universe v.
Write U₀(X)=X and U_(n+1)(X)=C(G,U_n(X)), with compact-open
topologies and diagonal G-actions.
For c ∈ U_(n+1)(X), the homogeneous resolution differential gives
E_(n+2)(d c)(t)=∑_(j=0)^(n+1) (-1)^j •
E_(n+1)(c)(t with coordinate j deleted). -/
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

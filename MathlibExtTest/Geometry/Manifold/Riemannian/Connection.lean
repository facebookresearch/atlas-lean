/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Geometry.Manifold.Riemannian.Connection

@[expose] public section

open Manifold

namespace MathlibExtTest.Geometry.Manifold.Riemannian.Connection

open MetaMathlibExt

-- Geometry 609: Christoffel symbols

/-The theorem proves the symmetry of Christoffel symbols meaning that Γᵏᵢⱼ = Γᵏⱼᵢ -/

theorem christoffelSymbols_symm
    {n} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ q i j, (g q) i j = (g q) j i)
    (p : EuclideanSpace ℝ (Fin n)) (k i j : Fin n) :
    christoffelSymbols g p k i j = christoffelSymbols g p k j i := by
  unfold christoffelSymbols
  simp only
  have hdl : ∀ l, fderiv ℝ (fun q => (g q) i j) p (EuclideanSpace.single l (1:ℝ)) =
                  fderiv ℝ (fun q => (g q) j i) p (EuclideanSpace.single l (1:ℝ)) := by
    intro l
    have hfun : (fun q : EuclideanSpace ℝ (Fin n) => (g q) i j) =
                (fun q => (g q) j i) := funext fun q => hg q i j
    rw [hfun]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [add_comm (fderiv ℝ _ _ _) (fderiv ℝ _ _ _)]
  rw [hdl l]

-- Geometry 610: Levi-Civita connection

/- In coordinate charts ∇₋w Z = -∇w Z -/

lemma leviCivita_neg
    {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (p : EuclideanSpace ℝ (Fin n))
    (W Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    leviCivitaConnectionChart (n := n) g p (fun q => - W q) Z =
    - leviCivitaConnectionChart (n := n) g p W Z := by
  unfold leviCivitaConnectionChart christoffelConnection
  simp [map_neg, Finset.sum_neg_distrib]
  abel

 /- On a Riemannian manifold ∇₋w Z = -∇w Z -/

lemma leviCivitaConnection_neg
    {M : Type*} {n : ℕ}
    [TopologicalSpace M]
    [Fintype (Fin n)] [DecidableEq (Fin n)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : ℕ∞) M]
    (e : PartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (W Z : M → EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ) :
    leviCivitaConnection (M := M) e (fun q => - W q) Z g =
    - leviCivitaConnection (M := M) e W Z g := by
  funext p
  unfold leviCivitaConnection
  exact leviCivita_neg g (e p) _ _

end MathlibExtTest.Geometry.Manifold.Riemannian.Connection

end

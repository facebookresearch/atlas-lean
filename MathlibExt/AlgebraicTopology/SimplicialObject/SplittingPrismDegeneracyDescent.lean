/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import MathlibExt.AlgebraicTopology.SimplexCategory.PrismMapDegeneracies

/-!
# Prism operators assembled from a simplicial splitting

Let s be a splitting of P in a category C, with nondegenerate summands N_n, and let Q be
simplicial. Specify maps p_{n,i} : N_n → Q_{n+1} for every i ∈ Fin(n+1). For an epimorphism
summand a : [n] → [m], prescribe the restriction of H_{n,i} : P_n → Q_{n+1} as p_{m,a(i)} ≫
Q(Φ(a,i).op), where Φ is the duplicated-vertex simplex map. The splitting coproduct defines H
uniquely from these restrictions.

For every epimorphism e : [n] → [m], P(e.op) ≫ H_{n,i} = H_{m,e(i)} ≫ Q(Φ(e,i).op). The two
elementary degeneracy formulas follow, including their equality cases. These operators provide
degeneracy-compatible data; their face equations are expressed separately. Object and morphism
universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.Splitting

variable {C : Type u} [Category.{v} C] {P Q : SimplicialObject C}
  (s : Splitting P)
  (p : ∀ n : ℕ, Fin (n + 1) → (s.N n ⟶ Q.obj (op ⦋n + 1⦌)))

/-- Prism operator defined on all splitting summands.

For a splitting s of P and maps p_{m,j} : N_m → Q_{m+1}, define H_{n,i} : P_n → Q_{n+1} by
coproduct descent. On the summand indexed by a : [n] → [m], its value is p_{m,a(i)} ≫
Q(Φ(a,i).op). -/
def prismDegree {n : ℕ} (i : Fin (n + 1)) :
    P.obj (op ⦋n⦌) ⟶ Q.obj (op ⦋n + 1⦌) :=
  s.desc (op ⦋n⦌) (fun a =>
    p a.1.unop.len (a.e.toOrderHom i) ≫
      Q.map (SimplexCategory.PrismMap.map a.e i).op)

/-- Summand formula for a descended prism operator.

For the cofan map ι_a : N_m → P_n indexed by an epimorphism a : [n] → [m], the operator
H_{n,i} satisfies ι_a ≫ H_{n,i} = p_{m,a(i)} ≫ Q(Φ(a,i).op). -/
@[reassoc]
theorem prismDegree_summand {n : ℕ} (i : Fin (n + 1)) (a : IndexSet (op ⦋n⦌)) :
    (s.cofan (op ⦋n⦌)).inj a ≫ s.prismDegree p i =
      p a.1.unop.len (a.e.toOrderHom i) ≫
        Q.map (SimplexCategory.PrismMap.map a.e i).op :=
  s.ι_desc (op ⦋n⦌) _ a

/-- Value of a prism operator on the nondegenerate summand.

For the distinguished cofan map ι_n : N_n → P_n, the descended prism operator satisfies ι_n ≫
H_{n,i} = p_{n,i}. This is the identity-epimorphism summand. -/
@[reassoc]
theorem prismDegree_distinguished {n : ℕ} (i : Fin (n + 1)) :
    s.ι n ≫ s.prismDegree p i = p n i := by
  have h := s.prismDegree_summand p i (IndexSet.id (op ⦋n⦌))
  rw [s.cofan_inj_id n] at h
  change s.ι n ≫ s.prismDegree p i =
    p n i ≫ Q.map (SimplexCategory.PrismMap.map (𝟙 ⦋n⦌) i).op at h
  have hMap := SimplexCategory.PrismMap.map_id i
  exact h.trans ((congrArg (fun e => p n i ≫ Q.map e.op) hMap).trans
    ((congrArg (fun e => p n i ≫ e) (Q.map_id (op ⦋n + 1⦌))).trans
      (Category.comp_id _)))

/-- Compatibility of descended prism operators with every simplex epimorphism.

For an epimorphism e : [n] → [m] and i ∈ Fin(n+1), P(e.op) ≫ H_{n,i} = H_{m,e(i)} ≫
Q(Φ(e,i).op). The equality holds for the splitting descent of any prescribed family p. -/
@[reassoc]
theorem prismDegree_epi {n m : ℕ} (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e] (i : Fin (n + 1)) :
    P.map e.op ≫ s.prismDegree p i =
      s.prismDegree p (e.toOrderHom i) ≫
        Q.map (SimplexCategory.PrismMap.map e i).op := by
  apply s.hom_ext'
  intro a
  have hNat := s.cofan_inj_epi_naturality a e.op
  have hNew := s.prismDegree_summand p i (a.epiComp e.op)
  dsimp only [IndexSet.epiComp] at hNew
  have hOld := s.prismDegree_summand p (e.toOrderHom i) a
  have hMap := SimplexCategory.PrismMap.map_comp e a.e i
  have hF : Q.map (SimplexCategory.PrismMap.map (e ≫ a.e) i).op =
      Q.map (SimplexCategory.PrismMap.map a.e (e.toOrderHom i)).op ≫
        Q.map (SimplexCategory.PrismMap.map e i).op := by
    rw [← hMap, op_comp]
    exact Q.map_comp _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ s.prismDegree p i) hNat).trans
      (hNew.trans
        ((congrArg (fun f => p a.1.unop.len (a.e.toOrderHom (e.toOrderHom i)) ≫ f) hF).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ Q.map (SimplexCategory.PrismMap.map e i).op) hOld.symm).trans
              (Category.assoc _ _ _))))))

/-- Degeneracy law with a right-shifted prism index.

For i,j ∈ Fin(n+1) with i ≤ j, the descended operators satisfy P.σ_i ≫ H_{n+1,j+1} = H_{n,j} ≫
Q.σ_i. The target degeneracy uses the unchanged index embedded by castSucc. -/
@[reassoc]
theorem prismDegree_degeneracy_castSucc {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    P.σ i ≫ s.prismDegree p j.succ = s.prismDegree p j ≫ Q.σ i.castSucc := by
  have h := s.prismDegree_epi p (SimplexCategory.σ i) j.succ
  rw [SimplexCategory.PrismMap.sigma_vertex_of_le i j hij,
    SimplexCategory.PrismMap.map_sigma_of_le i j hij] at h
  exact h

/-- Degeneracy law with a shifted target degeneracy index.

For i,j ∈ Fin(n+1) with j ≤ i, P.σ_i ≫ H_{n+1,j} = H_{n,j} ≫ Q.σ_{i+1}. The prism index embeds
by castSucc and the target degeneracy index by succ, including j = i. -/
@[reassoc]
theorem prismDegree_degeneracy_succ {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    P.σ i ≫ s.prismDegree p j.castSucc = s.prismDegree p j ≫ Q.σ i.succ := by
  have h := s.prismDegree_epi p (SimplexCategory.σ i) j.castSucc
  rw [SimplexCategory.PrismMap.sigma_vertex_of_ge i j hji,
    SimplexCategory.PrismMap.map_sigma_of_ge i j hji] at h
  exact h

end CategoryTheory.SimplicialObject.Splitting

end

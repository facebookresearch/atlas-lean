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
# General prism descent with every original degeneracy prescribed

Arbitrary maps on the nondegenerate summands of a native splitting determine
prism operators on the whole source in every degree. An original summand epi
acts through the existing canonical prism lift at the actual image of the
duplicated vertex. Native coproduct descent and composition of prism lifts
prove compatibility with every original epi, hence both native homotopy
degeneracy laws.

No face equation, endpoint equation, augmentation, or desired homotopy is
assumed. This is the degeneracy-preserving assembly component: the separate
ordered horn and final boundary construction must earn the primitive maps
and their face equations before these operators can form a homotopy.
Source proposals only; UNEXECUTED.
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

/-- The actual prism operator obtained from all original summand epis. -/
def prismDegree {n : ℕ} (i : Fin (n + 1)) :
    P.obj (op ⦋n⦌) ⟶ Q.obj (op ⦋n + 1⦌) :=
  s.desc (op ⦋n⦌) (fun a =>
    p a.1.unop.len (a.e.toOrderHom i) ≫
      Q.map (SimplexCategory.PrismMap.map a.e i).op)

/-- Every original degenerate summand uses its prescribed lower-degree prism. -/
@[reassoc]
theorem prismDegree_summand {n : ℕ} (i : Fin (n + 1)) (a : IndexSet (op ⦋n⦌)) :
    (s.cofan (op ⦋n⦌)).inj a ≫ s.prismDegree p i =
      p a.1.unop.len (a.e.toOrderHom i) ≫
        Q.map (SimplexCategory.PrismMap.map a.e i).op :=
  s.ι_desc (op ⦋n⦌) _ a

/-- The new nondegenerate summand retains its actual primitive prism map. -/
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

/-- All epi degeneracies commute with the actual prism prescription, in every
source degree and at every duplicated vertex. -/
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

/-- First native homotopy degeneracy law, earned without a face certificate. -/
@[reassoc]
theorem prismDegree_degeneracy_castSucc {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    P.σ i ≫ s.prismDegree p j.succ = s.prismDegree p j ≫ Q.σ i.castSucc := by
  have h := s.prismDegree_epi p (SimplexCategory.σ i) j.succ
  rw [SimplexCategory.PrismMap.sigma_vertex_of_le i j hij,
    SimplexCategory.PrismMap.map_sigma_of_le i j hij] at h
  exact h

/-- Second native homotopy degeneracy law, earned from the same epi descent. -/
@[reassoc]
theorem prismDegree_degeneracy_succ {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    P.σ i ≫ s.prismDegree p j.castSucc = s.prismDegree p j ≫ Q.σ i.succ := by
  have h := s.prismDegree_epi p (SimplexCategory.σ i) j.castSucc
  rw [SimplexCategory.PrismMap.sigma_vertex_of_ge i j hji,
    SimplexCategory.PrismMap.map_sigma_of_ge i j hji] at h
  exact h

end CategoryTheory.SimplicialObject.Splitting

end

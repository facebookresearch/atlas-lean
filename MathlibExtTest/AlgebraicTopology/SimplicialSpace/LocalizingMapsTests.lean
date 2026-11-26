/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMaps

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet.RezkTests

open Rezk

private abbrev edgeSimplex (n : ℕ) (i : Fin n) :
    (Δ[n] : SSet.{u}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.mkOfSucc i)

private abbrev longEdgeTwo : (Δ[2] : SSet.{u}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.diag 2)

private abbrev topSimplexTwo : (Δ[2] : SSet.{u}) _⦋2⦌ :=
  SSet.stdSimplex.objEquiv.symm (𝟙 _)

private theorem mem_spineSubcomplex_iff {n d : ℕ}
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (spineSubcomplex.{u} n).obj (op ⦋d⦌) ↔
      ∃ (i : Fin n) (f : ⦋d⦌ ⟶ ⦋1⦌),
        f ≫ SimplexCategory.mkOfSucc i = SSet.stdSimplex.objEquiv x := by
  simp only [spineSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨i, y, hy⟩
    refine ⟨i, SSet.stdSimplex.objEquiv y, ?_⟩
    apply SSet.stdSimplex.objEquiv.symm.injective
    rw [SSet.stdSimplex.objEquiv_symm_comp, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
    exact hy
  · rintro ⟨i, f, hf⟩
    refine ⟨i, SSet.stdSimplex.objEquiv.symm f, ?_⟩
    rw [← SSet.stdSimplex.objEquiv_symm_comp, hf,
      Equiv.symm_apply_apply]

private theorem edgeSimplex_mem (n : ℕ) (i : Fin n) :
    edgeSimplex.{u} n i ∈ (spineSubcomplex.{u} n).obj (op ⦋1⦌) := by
  apply (mem_spineSubcomplex_iff (edgeSimplex.{u} n i)).2
  exact ⟨i, 𝟙 _, Category.id_comp _⟩

private theorem longEdgeTwo_not_mem :
    longEdgeTwo.{u} ∉ (spineSubcomplex.{u} 2).obj (op ⦋1⦌) := by
  intro h
  obtain ⟨i, f, hf⟩ :=
    (mem_spineSubcomplex_iff (longEdgeTwo.{u})).1 h
  fin_cases i
  · have hval := congrArg
      (fun q : ⦋1⦌ ⟶ ⦋2⦌ => q.toOrderHom (1 : Fin 2)) hf
    change (SimplexCategory.mkOfSucc (0 : Fin 2)).toOrderHom
        (f.toOrderHom 1) = (2 : Fin 3) at hval
    let k : Fin 2 := f.toOrderHom 1
    change (SimplexCategory.mkOfSucc (0 : Fin 2)).toOrderHom k = 2 at hval
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · simp [hk] at hval
    · simp [hk] at hval
  · have hval := congrArg
      (fun q : ⦋1⦌ ⟶ ⦋2⦌ => q.toOrderHom (0 : Fin 2)) hf
    change (SimplexCategory.mkOfSucc (1 : Fin 2)).toOrderHom
        (f.toOrderHom 0) = (0 : Fin 3) at hval
    let k : Fin 2 := f.toOrderHom 0
    change (SimplexCategory.mkOfSucc (1 : Fin 2)).toOrderHom k = 0 at hval
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · simp [hk] at hval
    · simp [hk] at hval

private theorem topSimplexTwo_not_mem :
    topSimplexTwo.{u} ∉ (spineSubcomplex.{u} 2).obj (op ⦋2⦌) := by
  intro h
  obtain ⟨i, f, hf⟩ :=
    (mem_spineSubcomplex_iff (topSimplexTwo.{u})).1 h
  fin_cases i
  · have hval := congrArg
      (fun q : ⦋2⦌ ⟶ ⦋2⦌ => q.toOrderHom (2 : Fin 3)) hf
    change (SimplexCategory.mkOfSucc (0 : Fin 2)).toOrderHom
        (f.toOrderHom 2) = (2 : Fin 3) at hval
    let k : Fin 2 := f.toOrderHom 2
    change (SimplexCategory.mkOfSucc (0 : Fin 2)).toOrderHom k = 2 at hval
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · simp [hk] at hval
    · simp [hk] at hval
  · have hval := congrArg
      (fun q : ⦋2⦌ ⟶ ⦋2⦌ => q.toOrderHom (0 : Fin 3)) hf
    change (SimplexCategory.mkOfSucc (1 : Fin 2)).toOrderHom
        (f.toOrderHom 0) = (0 : Fin 3) at hval
    let k : Fin 2 := f.toOrderHom 0
    change (SimplexCategory.mkOfSucc (1 : Fin 2)).toOrderHom k = 0 at hval
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · simp [hk] at hval
    · simp [hk] at hval

private theorem spineSubcomplex_zero :
    spineSubcomplex.{u} 0 = ⊥ := by
  simp [spineSubcomplex]

private theorem spineSubcomplex_one :
    spineSubcomplex.{u} 1 = ⊤ := by
  simp [spineSubcomplex, SimplexCategory.mkOfSucc_eq_id,
    Subfunctor.range_id]

example : edgeSimplex.{u} 2 (0 : Fin 2) ∈
    (spineSubcomplex.{u} 2).obj (op ⦋1⦌) := edgeSimplex_mem 2 0

example : edgeSimplex.{u} 2 (1 : Fin 2) ∈
    (spineSubcomplex.{u} 2).obj (op ⦋1⦌) := edgeSimplex_mem 2 1

example : longEdgeTwo.{u} ∉
    (spineSubcomplex.{u} 2).obj (op ⦋1⦌) := longEdgeTwo_not_mem

example : topSimplexTwo.{u} ∉
    (spineSubcomplex.{u} 2).obj (op ⦋2⦌) := topSimplexTwo_not_mem

example : spineSubcomplex.{u} 0 = ⊥ := spineSubcomplex_zero

example : spineSubcomplex.{u} 1 = ⊤ := spineSubcomplex_one

example : ¬ ∃ n : {n : ℕ // 2 ≤ n}, n.1 = 0 := by
  rintro ⟨n, hn⟩
  omega

example : ¬ ∃ n : {n : ℕ // 2 ≤ n}, n.1 = 1 := by
  rintro ⟨n, hn⟩
  omega

example : walkingIsomorphismNerve.{u} = SSet.coherentIso.{u} := rfl

private theorem coherentIso_x₀_ne_x₁ :
    SSet.coherentIso.x₀.{u} ≠ SSet.coherentIso.x₁.{u} := by
  intro h
  have hobj := congrArg
    (fun z : SSet.coherentIso.{u} _⦋0⦌ => z.obj 0) h
  change CategoryTheory.WalkingIso.zero = CategoryTheory.WalkingIso.one at hobj
  have hbool := congrArg
    (fun z : CategoryTheory.WalkingIso.{u} => z.as.down) hobj
  change false = true at hbool
  contradiction

example : SSet.coherentIso.x₀.{u} ≠ SSet.coherentIso.x₁.{u} :=
  coherentIso_x₀_ne_x₁

example : SSet.Edge.{u} SSet.coherentIso.x₀ SSet.coherentIso.x₁ :=
  SSet.coherentIso.hom

example : SSet.Edge.{u} SSet.coherentIso.x₁ SSet.coherentIso.x₀ :=
  SSet.coherentIso.inv

example : SSet.Edge.CompStruct.{u} SSet.coherentIso.hom
    SSet.coherentIso.inv (SSet.Edge.id SSet.coherentIso.x₀) :=
  SSet.coherentIso.homInvId

example : SSet.Edge.CompStruct.{u} SSet.coherentIso.inv
    SSet.coherentIso.hom (SSet.Edge.id SSet.coherentIso.x₁) :=
  SSet.coherentIso.invHomId

example : completenessMap.{u} =
    SSet.simplicialSpaceDiscrete.map
      (SSet.yonedaEquiv.symm SSet.coherentIso.x₀) := rfl

example (n : ℕ) : spine.{u} n ⟶ representable.{u} n :=
  segalMap n

example : representable.{u} 0 ⟶ walkingIsomorphism.{u} :=
  completenessMap

section LocalizingBranches

variable (n : {n : ℕ // 2 ≤ n})

example : (localizingMap.{u} (.inl n)).left = spine.{u} n.1 := rfl

example : (localizingMap.{u} (.inl n)).right = representable.{u} n.1 := rfl

example : (localizingMap.{u} (.inl n)).hom = segalMap.{u} n.1 := rfl

example : (localizingMap.{u} (.inr PUnit.unit)).left = representable.{u} 0 := rfl

example : (localizingMap.{u} (.inr PUnit.unit)).right =
    walkingIsomorphism.{u} := rfl

example : (localizingMap.{u} (.inr PUnit.unit)).hom = completenessMap.{u} := rfl

end LocalizingBranches

section UniverseOne

example : (SSet.Rezk.spineSubcomplex.{1} 2 : SSet.{1}) ⟶ (Δ[2] : SSet.{1}) :=
  (SSet.Rezk.spineSubcomplex.{1} 2).ι

example : SSet.Rezk.spine.{1} 2 ⟶ SSet.Rezk.representable.{1} 2 :=
  SSet.Rezk.segalMap 2

example : Arrow (SimplicialObject SSet.{1}) :=
  SSet.Rezk.localizingMap (.inl ⟨2, by omega⟩)

end UniverseOne

section UniverseZero

example : (SSet.Rezk.spineSubcomplex.{0} 2 : SSet.{0}) ⟶ (Δ[2] : SSet.{0}) :=
  (SSet.Rezk.spineSubcomplex.{0} 2).ι

example : SSet.Rezk.representable.{0} 0 ⟶
    SSet.Rezk.walkingIsomorphism.{0} :=
  SSet.Rezk.completenessMap

example : Arrow (SimplicialObject SSet.{0}) :=
  SSet.Rezk.localizingMap (.inr PUnit.unit)

end UniverseZero

end SSet.RezkTests

/-! ## Explicit nonclaims and privacy guards -/

example : True := by
  fail_if_success
    have _ := SSet.Rezk.spineEdge_mem
  fail_if_success
    have _ := SSet.Rezk.segalComparison
  fail_if_success
    have _ := SSet.Rezk.completenessComparison
  fail_if_success
    have _ := SSet.Rezk.selectedLocalizingMap
  fail_if_success
    have _ := SSet.Rezk.isDerivedLocal
  fail_if_success
    have _ := SSet.Rezk.equivalenceEdges
  fail_if_success
    have _ := SSet.Rezk.rezkWeakEquivalences
  fail_if_success
    have _ := SSet.Rezk.joyalWeakEquivalences
  fail_if_success
    have _ := SSet.Rezk.localizingModelCategory
  trivial

#check SSet.Rezk.spineSubcomplex
#check SSet.Rezk.representable
#check SSet.Rezk.spine
#check SSet.Rezk.segalMap
#check SSet.Rezk.walkingIsomorphismNerve
#check SSet.Rezk.walkingIsomorphism
#check SSet.Rezk.completenessMap
#check SSet.Rezk.LocalizingIndex
#check SSet.Rezk.localizingMap

#print axioms SSet.Rezk.spineSubcomplex
#print axioms SSet.Rezk.representable
#print axioms SSet.Rezk.spine
#print axioms SSet.Rezk.segalMap
#print axioms SSet.Rezk.walkingIsomorphismNerve
#print axioms SSet.Rezk.walkingIsomorphism
#print axioms SSet.Rezk.completenessMap
#print axioms SSet.Rezk.LocalizingIndex
#print axioms SSet.Rezk.localizingMap

end

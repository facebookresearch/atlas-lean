/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupRestriction
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupCons
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupOneAnyProjection

/-!
# Corestriction of mixed iterated cup products

Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `A` a representation. A family `x :
Fin n → H¹(G,A)` and a final class `y ∈ H¹(H,Res A)` give an iterated cup of degree `n + 1` on
`H`. Its first `n` factors are the restrictions of the ambient classes. The coefficients are
identified either with `Res(A^{⊗(n+1)})` or with `Res P_n`, where `P₀=A` and `P_{n+1}=A ⊗
P_n`.

The tensor-power form has explicit one-factor and head-tail identities. If `H` has finite
index, canonical corestriction of the right-associated form equals the ambient
right-associated cup with the same initial classes and final factor `cor¹(y)`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (H : Subgroup G) [H.FiniteIndex]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, and `n : ℕ`. For `x : Fin
n → H¹(G,A)` and `y ∈ H¹(H,Res A)`, `restrictedIteratedCupClassSuccLast H A n x y` is the
iterated cup of the restricted `x`-classes followed by `y`, with degree `n + 1` and
coefficient `Rep.res H.subtype (TensorPower.tensorPowObj A (n + 1))`. -/
noncomputable def restrictedIteratedCupClassSuccLast
    (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    groupCohomology
      (Rep.res H.subtype
        (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  restrictedIteratedCupClassSuccLastOfHom H.subtype A n x y

omit [H.FiniteIndex] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, and `y ∈ H¹(H,Res A)`.
With no initial ambient factors, `restrictedIteratedCupClassSuccLast H A 0 (fun i => Fin.elim0
i) y = (Res((TensorPower.tensorPowObjOneIso A).inv))_* y`. Thus the result is `y` transported
to the coefficient `Res(A^{⊗1})`. -/
theorem restrictedIteratedCupClassSuccLast_zero
    (A : Rep k G)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassSuccLast H A 0
        (fun i => Fin.elim0 i) y =
      groupCohomology.map (MonoidHom.id H)
        ((Rep.resFunctor H.subtype).map
          (TensorPower.tensorPowObjOneIso A).inv) 1 y := by
  exact restrictedIteratedCupClassSuccLastOfHom_zero
    H.subtype A (fun i => Fin.elim0 i) y

omit [H.FiniteIndex] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `A : Rep k G`, `n : ℕ`, `x : Fin (n + 1)
→ H¹(G,A)`, and `y ∈ H¹(H,Res A)`. Applying `(Rep.resTensorPowHeadTailIso H.subtype A n).hom`
in degree `n + 2` to the mixed tensor-power cup equals `cupOneAny (Res A) (Res(A^{⊗(n+1)})) (n
+ 1) (res(x 0) ⊗ restrictedIteratedCupClassSuccLast H A n (fun i => x i.succ) y)`. -/
theorem restrictedIteratedCupClassSuccLast_succ_headTail
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso H.subtype A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSuccLast H A (n + 1) x y) =
      cupOneAny (Rep.res H.subtype A)
        (Rep.res H.subtype
          (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (groupCohomology.map H.subtype
            (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassSuccLast H A n
            (fun i => x i.succ) y) := by
  exact restrictedIteratedCupClassSuccLastOfHom_succ_headTail
    H.subtype A n x y

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `y ∈
H¹(H,Res A)`. Degree-one Schreier corestriction with coefficient `A^{⊗1}` sends
`restrictedIteratedCupClassSuccLast H A 0 (fun i => Fin.elim0 i) y` to `iteratedCupClassSucc A
0 ![corestrictionH1 A y]`, the one-factor ambient class in the same tensor-power coefficient. -/
theorem schreierCorestriction_restrictedIteratedCupClassSuccLast_zero
    (A : Rep k G)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    schreierCorestriction H (TensorPower.tensorPowObj A 1) 1
        (restrictedIteratedCupClassSuccLast H A 0
          (fun i => Fin.elim0 i) y) =
      iteratedCupClassSucc A 0
        ![groupCohomology.corestrictionH1 A y] := by
  rw [restrictedIteratedCupClassSuccLast_zero]
  rw [iteratedCupClassSucc_zero]
  have hnat := ConcreteCategory.congr_hom
    (schreierCorestriction_naturality H
      (TensorPower.tensorPowObjOneIso A).inv 1) y
  simp only [ConcreteCategory.comp_apply] at hnat
  have hone : (schreierCorestriction H A 1).hom y =
      groupCohomology.corestrictionH1 A y :=
    congrArg (fun f => f y) (schreierCorestriction_one_eq (H := H) A)
  rw [hone] at hnat
  exact hnat.symm

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `A : Rep k G`. Define `P₀=A` and
`P_{n+1}=A ⊗ P_n`. For `x : Fin n → H¹(G,A)` and `y ∈ H¹(H,Res A)`, the mixed class lies in
`H^{n+1}(H,Res P_n)`. It is `y` when `n=0`; its successor is the cup of `res(x 0)` with the
mixed tail, followed by `Res A ⊗ Res P_n → Res(A ⊗ P_n)`. -/
noncomputable def restrictedIteratedCupClassConsLast
    (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 (Rep.res H.subtype A)),
      groupCohomology
        (Rep.res H.subtype
          (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
  | n, x, y =>
      restrictedIteratedCupClassConsLastOfHom H.subtype A n x y

omit [H.FiniteIndex] in
@[simp]
theorem restrictedIteratedCupClassConsLast_zero
    (A : Rep k G) (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassConsLast H A 0 x y = y :=
  restrictedIteratedCupClassConsLastOfHom_zero H.subtype A x y

omit [H.FiniteIndex] in
@[simp]
theorem restrictedIteratedCupClassConsLast_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res H.subtype A)) :
    restrictedIteratedCupClassConsLast H A (n + 1) x y =
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso H.subtype A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res H.subtype A)
          (Rep.res H.subtype
            (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map H.subtype
              (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLast H A n
              (fun i => x i.succ) y)) :=
  restrictedIteratedCupClassConsLastOfHom_succ H.subtype A n x y

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, `n : ℕ`, `x :
Fin n → H¹(G,A)`, and `y ∈ H¹(H,Res A)`. For `P_n = TensorPower.tensorPowObjRightSucc A n`,
`schreierCorestriction H P_n (n + 1) (restrictedIteratedCupClassConsLast H A n x y) =
iteratedCupClassConsLast A n x (corestrictionH1 A y)` in `H^{n+1}(G,P_n)`. -/
theorem schreierCorestriction_restrictedIteratedCupClassConsLast
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 (Rep.res H.subtype A)),
      schreierCorestriction H
          (TensorPower.tensorPowObjRightSucc A n) (n + 1)
          (restrictedIteratedCupClassConsLast H A n x y) =
        iteratedCupClassConsLast A n x
          (groupCohomology.corestrictionH1 A y)
  | 0, x, y => by
      rw [restrictedIteratedCupClassConsLast_zero,
        iteratedCupClassConsLast_zero]
      exact congrArg (fun f => f y)
        (schreierCorestriction_one_eq (H := H) A)
  | n + 1, x, y => by
      rw [restrictedIteratedCupClassConsLast_succ,
        iteratedCupClassConsLast_succ]
      change schreierCorestriction H
          (A ⊗ TensorPower.tensorPowObjRightSucc A n) (n + 2)
          (groupCohomology.map (MonoidHom.id H)
            (Rep.resTensorIso H.subtype A
              (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
            (cupOneAny (Rep.res H.subtype A)
              (Rep.res H.subtype
                (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
              (groupCohomology.map H.subtype
                  (𝟙 (Rep.res H.subtype A)) 1 (x 0) ⊗ₜ[k]
                restrictedIteratedCupClassConsLast H A n
                  (fun i => x i.succ) y))) = _
      rw [schreierCorestriction_cup_one_any]
      rw [schreierCorestriction_restrictedIteratedCupClassConsLast]

end groupCohomology

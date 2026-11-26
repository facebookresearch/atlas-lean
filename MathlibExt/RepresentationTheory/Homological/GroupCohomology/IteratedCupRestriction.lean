/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCup
public import MathlibExt.RepresentationTheory.Rep.ResTensor

/-!
# Positive iterated cups under group restriction

Let k be a commutative ring, f:H→G a group homomorphism, and A a k-linear G-representation in
universe u. For a tuple of n+1 classes in H¹(H,Res_f A), form the iterated cup over H and
transport its tensor coefficient along Res_f(P_{n+1}(A))≅P_{n+1}(Res_f A). The result has
coefficient Res_f(P_{n+1}(A)) and degree n+1.

The first-factor comparison separates this class into the first restricted coefficient class and
the iterated tail. A mixed construction uses n ambient classes in H¹(G,A), restricts them, and
appends an arbitrary final class in H¹(H,Res_f A). Its empty-prefix case is the final class
transported through the restricted one-factor isomorphism; each successor exposes the first
ambient restriction and the remaining mixed tail.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For n≥0 and x_i∈H¹(H,A_f), let
Φ_n:Res_f(P_{n+1}(A))≅P_{n+1}(A_f) be the tensor-restriction isomorphism. The restricted
iterated class is (Φ_n.inv)_*L_n^{A_f}(x) in H^{n+1}(H,Res_f(P_{n+1}(A))). The x_i may be
arbitrary source-group classes. -/
noncomputable def restrictedIteratedCupClassSucc
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology (Rep.res f A) 1) :
    groupCohomology
      (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  (map (MonoidHom.id H)
    (Rep.resTensorPowIsoSucc f (Iso.refl (Rep.res f A)) n).inv
    (n + 1)).hom
      (iteratedCupClassSucc (Rep.res f A) n x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For n≥0 and x₀,…,x_{n+1}∈H¹(H,A_f), let L^f_n
denote the restricted tensor-coefficient iterated cup and
ψ^f_n:Res_f(P_{n+2}(A))≅A_f⊗Res_f(P_{n+1}(A)). Then
(ψ^f_n.hom)_*L^f_{n+1}(x)=x₀∪L^f_n(x₁,…,x_{n+1}) in degree n+2. -/
theorem restrictedIteratedCupClassSucc_headTail
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology (Rep.res f A) 1) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSucc f A (n + 1) x) =
      cupOneAny (Rep.res f A)
        (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (x 0 ⊗ₜ[k]
          restrictedIteratedCupClassSucc f A n (fun i => x i.succ)) := by
  let eTail := Rep.resTensorPowIsoSucc f
    (Iso.refl (Rep.res f A)) n
  unfold restrictedIteratedCupClassSucc
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.resTensorPowIsoSucc_inv_comp_resTensorPowHeadTailIso_hom]
  rw [map_id_comp]
  simp only [ConcreteCategory.comp_apply]
  rw [iteratedCupClassSucc_headTail]
  have hnat := ConcreteCategory.congr_hom
    (cupOneAny_naturality
      (𝟙 (Rep.res f A)) eTail.inv (n + 1))
    (x 0 ⊗ₜ[k]
      iteratedCupClassSucc (Rep.res f A) n (fun i => x i.succ))
  rw [map_id] at hnat
  convert hnat using 1
  simp only [eTail, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    ConcreteCategory.id_apply]

/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For n≥0, ambient classes
x₀,…,x_{n-1}∈H¹(G,A), and y∈H¹(H,A_f), form the ordered tuple (res_f x₀,…,res_f x_{n-1},y). Its
restricted iterated cup lies in H^{n+1}(H,Res_f(P_{n+1}(A))), with y as the distinguished final
entry. -/
noncomputable def restrictedIteratedCupClassSuccLastOfHom
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    groupCohomology
      (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1) :=
  restrictedIteratedCupClassSucc f A n
    (Fin.snoc
      (fun i => groupCohomology.map f
        (𝟙 (Rep.res f A)) 1 (x i)) y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For y∈H¹(H,A_f), the mixed construction with
no ambient inputs equals (Res_f(s.inv))_*y, where s:P₁(A)≅A is the one-factor comparison. The
result has degree one and coefficient Res_f(P₁(A)). -/
theorem restrictedIteratedCupClassSuccLastOfHom_zero
    (f : H →* G) (A : Rep k G)
    (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassSuccLastOfHom f A 0
        x y =
      groupCohomology.map (MonoidHom.id H)
        ((Rep.resFunctor f).map
          (TensorPower.tensorPowObjOneIso A).inv) 1 y := by
  have hx : x = (fun i => Fin.elim0 i) := by
    funext i
    exact Fin.elim0 i
  rw [hx]
  unfold restrictedIteratedCupClassSuccLastOfHom
    restrictedIteratedCupClassSucc
  rw [iteratedCupClassSucc_zero]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.tensorPowObjOneIso_inv_comp_resTensorPowIsoSucc_zero_inv]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. Let M_n(x,y) be the mixed restricted cup of n
ambient inputs and final source-group class y. For n≥0, x₀,…,x_n∈H¹(G,A), and y∈H¹(H,A_f), the
comparison ψ^f_n:Res_f(P_{n+2}(A))≅A_f⊗Res_f(P_{n+1}(A)) satisfies
(ψ^f_n.hom)_*M_{n+1}(x,y)=res_f(x₀)∪M_n(x₁,…,x_n,y), in degree n+2. -/
theorem restrictedIteratedCupClassSuccLastOfHom_succ_headTail
    (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSuccLastOfHom f A (n + 1) x y) =
      cupOneAny (Rep.res f A)
        (Rep.res f (TensorPower.tensorPowObj A (n + 1))) (n + 1)
        (groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassSuccLastOfHom f A n
            (fun i => x i.succ) y) := by
  let z : Fin (n + 2) → groupCohomology.H1 (Rep.res f A) :=
    Fin.snoc
      (fun i => groupCohomology.map f
        (𝟙 (Rep.res f A)) 1 (x i)) y
  have hz0 : z 0 = groupCohomology.map f
      (𝟙 (Rep.res f A)) 1 (x 0) := by
    simp [z]
  have hztail : (fun i => z i.succ) =
      Fin.snoc
        (fun i => groupCohomology.map f
          (𝟙 (Rep.res f A)) 1 (x i.succ)) y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [z]
    · change Fin.snoc
          (α := fun _ => groupCohomology.H1 (Rep.res f A))
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y
          j.succ.castSucc = _
      rw [Fin.snoc_castSucc]
      rw [Fin.snoc_castSucc]
  unfold restrictedIteratedCupClassSuccLastOfHom
  change (map (MonoidHom.id H)
      (Rep.resTensorPowHeadTailIso f A n).hom (n + 2)).hom
        (restrictedIteratedCupClassSucc f A (n + 1) z) = _
  rw [restrictedIteratedCupClassSucc_headTail, hz0, hztail]

end groupCohomology

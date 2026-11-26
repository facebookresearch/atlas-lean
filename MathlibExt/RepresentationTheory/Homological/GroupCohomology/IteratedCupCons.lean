/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.IteratedCupRestriction

/-!
# Right-associated positive iterated cups

Let k be a commutative ring, G a group, and A a k-linear representation in universe u. Put
R₀(A)=A and R_{n+1}(A)=A⊗R_n(A). The right-associated iterated cup C_n(x) of n+1 degree-one
classes lies in H^{n+1}(G,R_n(A)); at each successor it cups the first class with the
recursively formed tail.

The canonical reassociation P_{n+1}(A)≅R_n(A) identifies C_n with the left-associated ordered
cup L_n. A variant keeps a distinguished final class after n prefix entries.

For f:H→G, ambient prefix classes may be restricted and followed by a source-group class.
Tensor-restriction isomorphisms compare the result with the right-associated power of Res_f A.
Reassociation of the ambient power then recovers the restricted left-associated iterated cup.
All constructions retain the tuple order and have positive cohomological degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A), and let C_n(x)∈H^{n+1}(G,R_n(A)) be the right-associated
iterated cup. For n≥0 and x₀,…,x_n∈H¹(G,A), define C₀([x₀])=x₀ and
C_{n+1}(x)=x₀∪C_n(x₁,…,x_{n+1}). The successor has coefficient A⊗R_n(A)=R_{n+1}(A) and degree
n+2. -/
noncomputable def iteratedCupClassCons (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin (n + 1) → groupCohomology.H1 A),
      groupCohomology
        (TensorPower.tensorPowObjRightSucc A n) (n + 1)
  | 0, x => x 0
  | n + 1, x =>
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassCons A n (fun i => x i.succ))

@[simp]
theorem iteratedCupClassCons_zero
    (A : Rep k G) (x : Fin 1 → groupCohomology.H1 A) :
    iteratedCupClassCons A 0 x = x 0 :=
  rfl

@[simp]
theorem iteratedCupClassCons_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology.H1 A) :
    iteratedCupClassCons A (n + 1) x =
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassCons A n (fun i => x i.succ)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A), and let C_n(x)∈H^{n+1}(G,R_n(A)) be the right-associated
iterated cup. Let L_n(x) be the left-associated cup with coefficient P_{n+1}(A), and
χ_n:P_{n+1}(A)≅R_n(A) its canonical reassociation. For n≥0 and x₀,…,x_n∈H¹(G,A),
(χ_n.hom)_*L_n(x)=C_n(x). -/
theorem iteratedCupClassSucc_to_cons
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin (n + 1) → groupCohomology.H1 A),
      (map (MonoidHom.id G)
        (TensorPower.tensorPowObjRightSuccIso A n).hom (n + 1)).hom
          (iteratedCupClassSucc A n x) =
        iteratedCupClassCons A n x
  | 0, x => by
      rw [iteratedCupClassSucc_zero]
      rw [TensorPower.tensorPowObjRightSuccIso_zero]
      rw [← ConcreteCategory.comp_apply, ← map_id_comp]
      rw [Iso.inv_hom_id]
      change (map (MonoidHom.id G) (𝟙 A) 1).hom (x 0) = x 0
      rw [map_id]
      rfl
  | n + 1, x => by
      rw [TensorPower.tensorPowObjRightSuccIso_succ]
      simp only [Iso.trans_hom]
      rw [map_id_comp]
      simp only [ConcreteCategory.comp_apply]
      rw [iteratedCupClassSucc_headTail]
      have hnat := ConcreteCategory.congr_hom
        (cupOneAny_naturality
          (𝟙 A) (TensorPower.tensorPowObjRightSuccIso A n).hom (n + 1))
        (x 0 ⊗ₜ[k]
          iteratedCupClassSucc A n (fun i => x i.succ))
      rw [map_id] at hnat
      have hnat_apply :
          (map (MonoidHom.id G)
            (𝟙 A ⊗ₘ (TensorPower.tensorPowObjRightSuccIso A n).hom)
            (n + 2)).hom
            (cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
              (x 0 ⊗ₜ[k]
                iteratedCupClassSucc A n (fun i => x i.succ))) =
          cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
            (x 0 ⊗ₜ[k]
              (map (MonoidHom.id G)
                (TensorPower.tensorPowObjRightSuccIso A n).hom
                (n + 1)).hom
                (iteratedCupClassSucc A n (fun i => x i.succ))) := by
        convert hnat using 1
        all_goals rfl
      change (map (MonoidHom.id G)
          (𝟙 A ⊗ₘ (TensorPower.tensorPowObjRightSuccIso A n).hom)
          (n + 2)).hom
          (cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
            (x 0 ⊗ₜ[k]
              iteratedCupClassSucc A n (fun i => x i.succ))) = _
      rw [hnat_apply, iteratedCupClassSucc_to_cons]
      rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A), and let C_n(x)∈H^{n+1}(G,R_n(A)) be the right-associated
iterated cup. For n≥0 and x₀,…,x_n∈H¹(G,A), let χ_n:P_{n+1}(A)≅R_n(A). The inverse comparison
satisfies (χ_n.inv)_*C_n(x)=L_n(x) in H^{n+1}(G,P_{n+1}(A)). -/
theorem iteratedCupClassCons_to_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjRightSuccIso A n).inv (n + 1)).hom
        (iteratedCupClassCons A n x) =
      iteratedCupClassSucc A n x := by
  rw [← iteratedCupClassSucc_to_cons]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Iso.hom_inv_id]
  change (map (MonoidHom.id G)
    (𝟙 (TensorPower.tensorPowObj A (n + 1))) (n + 1)).hom
      (iteratedCupClassSucc A n x) = _
  rw [map_id]
  rfl

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A), and let C_n(x)∈H^{n+1}(G,R_n(A)) be the right-associated
iterated cup. For n≥0, a prefix x₀,…,x_{n-1} and final class y in H¹(G,A), define D₀([],y)=y and
D_{n+1}(x,y)=x₀∪D_n(tail x,y). The class D_n has degree n+1 and coefficient R_n(A). -/
noncomputable def iteratedCupClassConsLast (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 A),
      groupCohomology
        (TensorPower.tensorPowObjRightSucc A n) (n + 1)
  | 0, _, y => y
  | n + 1, x, y =>
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassConsLast A n (fun i => x i.succ) y)

/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A). For n
ambient classes x_i∈H¹(G,A) and y∈H¹(H,A_f), the mixed class D^f_n(x,y) lies in
H^{n+1}(H,Res_f(R_n(A))). Its empty prefix is y. Each successor cups res_f(x₀) with D^f_n(tail
x,y), then applies A_f⊗Res_f(R_n(A))≅Res_f(R_{n+1}(A)). -/
noncomputable def restrictedIteratedCupClassConsLastOfHom
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ∀ (n : ℕ) (_x : Fin n → groupCohomology.H1 A)
      (_y : groupCohomology.H1 (Rep.res f A)),
      groupCohomology
        (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
  | 0, _, y => y
  | n + 1, x, y =>
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso f A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res f A)
          (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map f
              (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLastOfHom f A n
              (fun i => x i.succ) y))

@[simp]
theorem iteratedCupClassConsLast_zero
    (A : Rep k G) (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    iteratedCupClassConsLast A 0 x y = y :=
  rfl

@[simp]
theorem iteratedCupClassConsLast_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    iteratedCupClassConsLast A (n + 1) x y =
      cupOneAny A (TensorPower.tensorPowObjRightSucc A n) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassConsLast A n (fun i => x i.succ) y) :=
  rfl

@[simp]
theorem restrictedIteratedCupClassConsLastOfHom_zero
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (x : Fin 0 → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassConsLastOfHom f A 0 x y = y :=
  rfl

@[simp]
theorem restrictedIteratedCupClassConsLastOfHom_succ
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    restrictedIteratedCupClassConsLastOfHom f A (n + 1) x y =
      groupCohomology.map (MonoidHom.id H)
        (Rep.resTensorIso f A
          (TensorPower.tensorPowObjRightSucc A n)).hom (n + 2)
        (cupOneAny (Rep.res f A)
          (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
          (groupCohomology.map f
              (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
            restrictedIteratedCupClassConsLastOfHom f A n
              (fun i => x i.succ) y)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. Let R₀(B)=B, R_{n+1}(B)=B⊗R_n(B), and
λ_n:Res_f(R_n(A))≅R_n(A_f) be the tensor-restriction comparison. For n ambient inputs
x_i∈H¹(G,A) and y∈H¹(H,A_f), (λ_n.hom)_*D^f_n(x,y)=D_n^{A_f}(res_f x₀,…,res_f x_{n-1},y), with
degree n+1. -/
theorem restrictedIteratedCupClassConsLastOfHom_to_native
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 (Rep.res f A)),
      (map (MonoidHom.id H)
        (Rep.resTensorPowRightSuccIso f
          (Iso.refl (Rep.res f A)) n).hom (n + 1)).hom
          (restrictedIteratedCupClassConsLastOfHom f A n x y) =
        iteratedCupClassConsLast (Rep.res f A) n
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y
  | 0, x, y => by
      rw [restrictedIteratedCupClassConsLastOfHom_zero,
        iteratedCupClassConsLast_zero,
        Rep.resTensorPowRightSuccIso_zero]
      change (map (MonoidHom.id H) (𝟙 (Rep.res f A)) 1).hom y = y
      rw [map_id]
      rfl
  | n + 1, x, y => by
      rw [restrictedIteratedCupClassConsLastOfHom_succ,
        iteratedCupClassConsLast_succ,
        Rep.resTensorPowRightSuccIso_succ]
      simp only [Iso.trans_hom, Iso.symm_hom]
      dsimp only [TensorPower.tensorPowObjRightSucc]
      rw [← ConcreteCategory.comp_apply, ← map_id_comp]
      have hcoeff :
          (Rep.resTensorIso f A
              (TensorPower.tensorPowObjRightSucc A n)).hom ≫
            ((Rep.resTensorIso f A
              (TensorPower.tensorPowObjRightSucc A n)).inv ≫
              (tensorIso (Iso.refl (Rep.res f A))
                (Rep.resTensorPowRightSuccIso f
                  (Iso.refl (Rep.res f A)) n)).hom) =
          (tensorIso (Iso.refl (Rep.res f A))
            (Rep.resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n)).hom := by
        simp
      rw [hcoeff]
      have htensor :
          (tensorIso (Iso.refl (Rep.res f A))
            (Rep.resTensorPowRightSuccIso f
              (Iso.refl (Rep.res f A)) n)).hom =
            𝟙 (Rep.res f A) ⊗ₘ
              (Rep.resTensorPowRightSuccIso f
                (Iso.refl (Rep.res f A)) n).hom :=
        rfl
      rw [htensor]
      have hnat := ConcreteCategory.congr_hom
        (cupOneAny_naturality
          (𝟙 (Rep.res f A))
          (Rep.resTensorPowRightSuccIso f
            (Iso.refl (Rep.res f A)) n).hom (n + 1))
        (groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
          restrictedIteratedCupClassConsLastOfHom f A n
            (fun i => x i.succ) y)
      rw [map_id] at hnat
      have hnat_apply :
          (map (MonoidHom.id H)
            (𝟙 (Rep.res f A) ⊗ₘ
              (Rep.resTensorPowRightSuccIso f
                (Iso.refl (Rep.res f A)) n).hom) (n + 2)).hom
            (cupOneAny (Rep.res f A)
              (Rep.res f (TensorPower.tensorPowObjRightSucc A n)) (n + 1)
              (groupCohomology.map f
                  (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
                restrictedIteratedCupClassConsLastOfHom f A n
                  (fun i => x i.succ) y)) =
          cupOneAny (Rep.res f A)
              (TensorPower.tensorPowObjRightSucc (Rep.res f A) n) (n + 1)
            (groupCohomology.map f
                (𝟙 (Rep.res f A)) 1 (x 0) ⊗ₜ[k]
              (map (MonoidHom.id H)
                (Rep.resTensorPowRightSuccIso f
                  (Iso.refl (Rep.res f A)) n).hom (n + 1)).hom
                (restrictedIteratedCupClassConsLastOfHom f A n
                  (fun i => x i.succ) y)) := by
        convert hnat using 1
        all_goals rfl
      refine hnat_apply.trans ?_
      rw [restrictedIteratedCupClassConsLastOfHom_to_native]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For n≥0, ambient x_i∈H¹(G,A), y∈H¹(H,A_f),
and λ_n:Res_f(R_n(A))≅R_n(A_f), the mixed cup satisfies (λ_n.inv)_*D_n^{A_f}(res_f x₀,…,res_f
x_{n-1},y)=D^f_n(x,y). The result has coefficient Res_f(R_n(A)) and degree n+1. -/
theorem restrictedIteratedCupClassConsLastOfHom_from_native
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (n : ℕ) (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      (Rep.resTensorPowRightSuccIso f
        (Iso.refl (Rep.res f A)) n).inv (n + 1)).hom
        (iteratedCupClassConsLast (Rep.res f A) n
          (fun i => groupCohomology.map f
            (𝟙 (Rep.res f A)) 1 (x i)) y) =
      restrictedIteratedCupClassConsLastOfHom f A n x y := by
  rw [← restrictedIteratedCupClassConsLastOfHom_to_native]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Iso.hom_inv_id]
  change (map (MonoidHom.id H)
    (𝟙 (Rep.res f (TensorPower.tensorPowObjRightSucc A n)))
    (n + 1)).hom
      (restrictedIteratedCupClassConsLastOfHom f A n x y) = _
  rw [map_id]
  rfl

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Put R₀(A)=A and R_{n+1}(A)=A⊗R_n(A), and let C_n(x)∈H^{n+1}(G,R_n(A)) be the right-associated
iterated cup. For n≥0, x indexed by {0,…,n-1}, and y∈H¹(G,A), the distinguished-final recursion
D_n(x,y) equals C_n(x₀,…,x_{n-1},y). Both classes have coefficient R_n(A) and degree n+1. -/
theorem iteratedCupClassConsLast_eq_snoc
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin n → groupCohomology.H1 A)
      (y : groupCohomology.H1 A),
      iteratedCupClassConsLast A n x y =
        iteratedCupClassCons A n (Fin.snoc x y)
  | 0, x, y => by
      rw [iteratedCupClassConsLast_zero, iteratedCupClassCons_zero]
      change y = Fin.snoc (α := fun _ => groupCohomology.H1 A)
        x y (Fin.last 0)
      rw [Fin.snoc_last]
  | n + 1, x, y => by
      have hz0 : Fin.snoc (α := fun _ => groupCohomology.H1 A)
          x y 0 = x 0 := by
        change Fin.snoc (α := fun _ => groupCohomology.H1 A)
          x y (0 : Fin (n + 1)).castSucc = x 0
        rw [Fin.snoc_castSucc]
      have hztail : (fun i => Fin.snoc
          (α := fun _ => groupCohomology.H1 A) x y i.succ) =
          Fin.snoc (α := fun _ => groupCohomology.H1 A)
            (fun i => x i.succ) y := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · change Fin.snoc (α := fun _ => groupCohomology.H1 A)
            x y j.succ.castSucc = _
          rw [Fin.snoc_castSucc]
          rw [Fin.snoc_castSucc]
      rw [iteratedCupClassConsLast_succ, iteratedCupClassCons_succ,
        hz0, hztail, iteratedCupClassConsLast_eq_snoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For n≥0, prefix x₀,…,x_{n-1}, final y∈H¹(G,A), and χ_n:P_{n+1}(A)≅R_n(A), one has
(χ_n.inv)_*D_n(x,y)=L_n(x₀,…,x_{n-1},y). The target is H^{n+1}(G,P_{n+1}(A)). -/
theorem iteratedCupClassConsLast_to_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 A) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjRightSuccIso A n).inv (n + 1)).hom
        (iteratedCupClassConsLast A n x y) =
      iteratedCupClassSucc A n (Fin.snoc x y) := by
  rw [iteratedCupClassConsLast_eq_snoc]
  exact iteratedCupClassCons_to_succ A n (Fin.snoc x y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:H→G a homomorphism of groups in the given universe u, and A a
k-linear G-representation. Write A_f=Res_f A, P_m(A) for its left-associated m-fold tensor
coefficient, and res_f for cohomology restriction. For n≥0, ambient inputs x_i∈H¹(G,A), final
y∈H¹(H,A_f), and χ_n:P_{n+1}(A)≅R_n(A), one has (Res_f(χ_n.inv))_*D^f_n(x,y)=M_n(x,y). Here
D^f_n has coefficient Res_f(R_n(A)), and M_n is the mixed left-associated cup with coefficient
Res_f(P_{n+1}(A)); both have degree n+1. -/
theorem restrictedIteratedCupClassConsLastOfHom_reassociate
    {H : Type u} [Group H] (f : H →* G) (A : Rep k G)
    (n : ℕ) (x : Fin n → groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res f A)) :
    (map (MonoidHom.id H)
      ((Rep.resFunctor f).map
        (TensorPower.tensorPowObjRightSuccIso A n).inv)
      (n + 1)).hom
        (restrictedIteratedCupClassConsLastOfHom f A n x y) =
      restrictedIteratedCupClassSuccLastOfHom f A n x y := by
  unfold restrictedIteratedCupClassSuccLastOfHom
    restrictedIteratedCupClassSucc
  rw [← restrictedIteratedCupClassConsLastOfHom_from_native]
  rw [iteratedCupClassConsLast_eq_snoc]
  rw [← iteratedCupClassSucc_to_cons]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Rep.resTensorPow_reassociation_coherence]

end groupCohomology

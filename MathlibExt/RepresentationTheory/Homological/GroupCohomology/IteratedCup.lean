/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.Multilinear.Curry
public import MathlibExt.CategoryTheory.Monoidal.TensorPowerFunctor
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneAnyAssociativity

/-!
# Ordered positive iterated cups

Let k be a commutative ring, G a group, and A a k-linear representation in universe u. A
nonempty tuple x₀,…,x_n∈H¹(G,A) has an ordered iterated cup L_n(x) in H^{n+1}(G,P_{n+1}(A)),
where P₀=I and P_{m+1}=P_m⊗A.

The one-factor comparison P₁(A)≅A transports x₀ into the weight-one coefficient. At each
successor, cup the preceding prefix with the final class. This gives a k-multilinear map in all
n+1 inputs. It is natural in coefficient morphisms and in simultaneous group restriction and
coefficient maps.

Canonical reassociation P_{n+2}(A)≅A⊗P_{n+1}(A) expresses L_{n+1} as the first class cupped with
the iterated tail. The two-factor and three-factor formulas recover ordinary binary and triple
cups with their coefficient isomorphisms. If the binary cup of any adjacent input pair is zero,
the complete ordered iterated cup is zero. All weights are positive, and reassociation
introduces no permutation of inputs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory

universe u

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For n≥0, there is a k-multilinear map (H¹(G,A))^{Fin(n+1)}→H^{n+1}(G,P_{n+1}(A)). At weight
one it is the coefficient transport by (P₁(A)≅A)⁻¹. The successor cups the preceding n+1 inputs
with the final degree-one class, retaining their order and left-associated tensor coefficient. -/
noncomputable def iteratedCupMultilinearSucc (A : Rep k G) :
    ∀ (n : ℕ),
      MultilinearMap k (fun _ : Fin (n + 1) => groupCohomology A 1)
        (groupCohomology (TensorPower.tensorPowObj A (n + 1)) (n + 1))
  | 0 => MultilinearMap.mk'
      (fun x => (map (MonoidHom.id G)
        (TensorPower.tensorPowObjOneIso A).inv 1).hom (x 0))
      (by
        intro x i a b
        fin_cases i
        exact (map (MonoidHom.id G)
          (TensorPower.tensorPowObjOneIso A).inv 1).hom.map_add a b)
      (by
        intro x i c a
        fin_cases i
        exact (map (MonoidHom.id G)
          (TensorPower.tensorPowObjOneIso A).inv 1).hom.map_smul c a)
  | n + 1 =>
      (TensorProduct.curry
        (cup G k (TensorPower.tensorPowObj A (n + 1)) A
          (n + 1) 1).hom).compMultilinearMap
          (iteratedCupMultilinearSucc A n) |>.uncurryRight

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For every
n≥0 and tuple x indexed by {0,…,n}, L_n(x) is evaluation of the k-multilinear iterated-cup map
on those inputs. The target degree and number of coefficient factors are both n+1. -/
noncomputable def iteratedCupClassSucc (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology A 1) :
    groupCohomology (TensorPower.tensorPowObj A (n + 1)) (n + 1) :=
  iteratedCupMultilinearSucc A n x

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For x∈H¹(G,A), let s:P₁(A)≅A be the canonical one-factor isomorphism. Then
L₀([x])=(s.inv)_*(x) in H¹(G,P₁(A)). The parameter zero denotes one input and cohomological
degree one. -/
@[simp]
theorem iteratedCupClassSucc_zero
    (A : Rep k G) (x : Fin 1 → groupCohomology A 1) :
    iteratedCupClassSucc A 0 x =
      (map (MonoidHom.id G)
        (TensorPower.tensorPowObjOneIso A).inv 1).hom (x 0) :=
  rfl

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0
and x₀,…,x_{n+1}∈H¹(G,A), L_{n+1}(x)=L_n(x₀,…,x_n)∪x_{n+1}. The cup has degrees (n+1,1) and
coefficient P_{n+1}(A)⊗A=P_{n+2}(A). -/
@[simp]
theorem iteratedCupClassSucc_succ
    (A : Rep k G) (n : ℕ)
    (x : Fin ((n + 1) + 1) → groupCohomology A 1) :
    iteratedCupClassSucc A (n + 1) x =
      (cup G k (TensorPower.tensorPowObj A (n + 1)) A (n + 1) 1).hom
        (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
          x (Fin.last (n + 1))) :=
  rfl

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0
and tuples x,y indexed by {0,…,n}, if x_i=y_i for every i, then L_n(x)=L_n(y) in
H^{n+1}(G,P_{n+1}(A)). -/
theorem iteratedCupClassSucc_congr
    (A : Rep k G) (n : ℕ)
    {x y : Fin (n + 1) → groupCohomology A 1}
    (h : ∀ i, x i = y i) :
    iteratedCupClassSucc A n x = iteratedCupClassSucc A n y := by
  apply congrArg (iteratedCupClassSucc A n)
  funext i
  exact h i

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0, a
tuple x, an index 0≤i≤n, and a,b∈H¹(G,A), one has L_n(x[i:=a+b])=L_n(x[i:=a])+L_n(x[i:=b]) in
H^{n+1}(G,P_{n+1}(A)). All other entries are retained. -/
theorem iteratedCupClassSucc_update_add
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology A 1) (i : Fin (n + 1))
    (a b : groupCohomology A 1) :
    iteratedCupClassSucc A n (Function.update x i (a + b)) =
      iteratedCupClassSucc A n (Function.update x i a) +
        iteratedCupClassSucc A n (Function.update x i b) :=
  (iteratedCupMultilinearSucc A n).map_update_add x i a b

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0, a
tuple x, 0≤i≤n, c∈k, and a∈H¹(G,A), L_n(x[i:=c•a])=c•L_n(x[i:=a]). The remaining entries and
tensor-coefficient order are retained. -/
theorem iteratedCupClassSucc_update_smul
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology A 1) (i : Fin (n + 1))
    (c : k) (a : groupCohomology A 1) :
    iteratedCupClassSucc A n (Function.update x i (c • a)) =
      c • iteratedCupClassSucc A n (Function.update x i a) :=
  (iteratedCupMultilinearSucc A n).map_update_smul x i c a

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, A,B k-linear G-representations, and f:A→B an equivariant
k-linear map, in universe u. For n≥0, its tensor-power map P_{n+1}(f) induces
(P_{n+1}(f))_*L_n^A(x)=L_n^B(f_*x₀,…,f_*x_n). The outer map has degree n+1 and each input map
degree one. -/
theorem iteratedCupClassSucc_naturality
    {A B : Rep k G} (f : A ⟶ B) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology A 1) :
    (map (MonoidHom.id G) (TensorPower.tensorPowMap f (n + 1))
      (n + 1)).hom (iteratedCupClassSucc A n x) =
      iteratedCupClassSucc B n
        (fun i => (map (MonoidHom.id G) f 1).hom (x i)) := by
  induction n with
  | zero =>
      rw [iteratedCupClassSucc_zero, iteratedCupClassSucc_zero]
      rw [← ConcreteCategory.comp_apply, ← map_id_comp]
      change (map (MonoidHom.id G)
          ((TensorPower.tensorPowObjOneIso A).inv ≫
            TensorPower.tensorPowMap f 1) 1).hom (x 0) = _
      have hCoeff :=
        (TensorPower.tensorPowObjOneIso_inv_naturality f).symm
      calc
        (map (MonoidHom.id G)
            ((TensorPower.tensorPowObjOneIso A).inv ≫
              TensorPower.tensorPowMap f 1) 1).hom (x 0) =
          (map (MonoidHom.id G)
            (f ≫ (TensorPower.tensorPowObjOneIso B).inv) 1).hom (x 0) :=
              congrArg (fun g => (map (MonoidHom.id G) g 1).hom (x 0)) hCoeff
        _ = _ := by
          rw [map_id_comp]
          rfl
  | succ n ih =>
      rw [iteratedCupClassSucc_succ, iteratedCupClassSucc_succ]
      rw [TensorPower.tensorPowMap_succ]
      let fPow := TensorPower.tensorPowMap f (n + 1)
      have hNat := cup_naturality (G := G) (k := k) fPow f (n + 1) 1
      have hApply := congrArg (fun g => g.hom
        (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
          x (Fin.last (n + 1)))) hNat
      change (map (MonoidHom.id G) (fPow ⊗ₘ f) (n + 1 + 1)).hom
          ((cup G k (TensorPower.tensorPowObj A (n + 1)) A
            (n + 1) 1).hom
            (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
              x (Fin.last (n + 1)))) =
        (cup G k (TensorPower.tensorPowObj B (n + 1)) B
          (n + 1) 1).hom
          ((map (MonoidHom.id G) fPow (n + 1)).hom
              (iteratedCupClassSucc A n (fun i => x i.castSucc)) ⊗ₜ[k]
            (map (MonoidHom.id G) f 1).hom (x (Fin.last (n + 1)))) at hApply
      change (map (MonoidHom.id G) (fPow ⊗ₘ f) (n + 1 + 1)).hom
          ((cup G k (TensorPower.tensorPowObj A (n + 1)) A
            (n + 1) 1).hom
            (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
              x (Fin.last (n + 1)))) = _
      rw [hApply, ih]

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, f:G→H a group homomorphism, A an H-representation, and φ:Res_f A→B
a coefficient morphism, in universe u. For n≥0, let Φ_{n+1}:Res_f(P_{n+1}(A))→P_{n+1}(B) be the
induced tensor-power coefficient map. Then
map_{f,Φ_{n+1}}(L_n^A(x))=L_n^B(map_{f,φ}(x₀),…,map_{f,φ}(x_n)), with degree n+1 on the left and
degree one on each input. -/
theorem iteratedCupClassSucc_naturality_of_hom
    {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (phi : Rep.res f A ⟶ B) (n : ℕ)
    (x : Fin (n + 1) → groupCohomology A 1) :
    (map f (Rep.resTensorPowMapSucc f phi n) (n + 1)).hom
        (iteratedCupClassSucc A n x) =
      iteratedCupClassSucc B n
        (fun i => (map f phi 1).hom (x i)) := by
  induction n with
  | zero =>
      rw [iteratedCupClassSucc_zero, iteratedCupClassSucc_zero]
      rw [← ConcreteCategory.comp_apply]
      rw [← map_comp]
      change (map ((MonoidHom.id H).comp f)
          ((Rep.resFunctor f).map (TensorPower.tensorPowObjOneIso A).inv ≫
            Rep.resTensorPowMapSucc f phi 0) 1).hom (x 0) = _
      have hCoeff :=
        Rep.tensorPowObjOneIso_inv_comp_resTensorPowMapSucc_zero f phi
      have hMap := congrArg (fun g =>
        (map ((MonoidHom.id H).comp f) g 1).hom (x 0)) hCoeff
      rw [hMap]
      have hGroupMap :
          map ((MonoidHom.id H).comp f)
              (phi ≫ (TensorPower.tensorPowObjOneIso B).inv) 1 =
            map (f.comp (MonoidHom.id G))
              ((Rep.resFunctor (MonoidHom.id G)).map phi ≫
                (TensorPower.tensorPowObjOneIso B).inv) 1 := by
        apply map_congr
        · ext
          simp
        · rfl
      rw [hGroupMap]
      have hComp := congrArg (fun g => g.hom (x 0))
        (map_comp f (MonoidHom.id G) phi
          (TensorPower.tensorPowObjOneIso B).inv 1)
      simpa using hComp
  | succ n ih =>
      rw [iteratedCupClassSucc_succ, iteratedCupClassSucc_succ]
      rw [Rep.resTensorPowMapSucc_succ]
      let fPow := Rep.resTensorPowMapSucc f phi n
      have hNat := cup_naturality_of_hom
        (k := k) f fPow phi (n + 1) 1
      have hApply := congrArg (fun g => g.hom
        (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
          x (Fin.last (n + 1)))) hNat
      change (map f
          ((Rep.resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
            (fPow ⊗ₘ phi)) (n + 1 + 1)).hom
          ((cup H k (TensorPower.tensorPowObj A (n + 1)) A
            (n + 1) 1).hom
            (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
              x (Fin.last (n + 1)))) =
        (cup G k (TensorPower.tensorPowObj B (n + 1)) B
          (n + 1) 1).hom
          ((map f fPow (n + 1)).hom
              (iteratedCupClassSucc A n (fun i => x i.castSucc)) ⊗ₜ[k]
            (map f phi 1).hom (x (Fin.last (n + 1)))) at hApply
      change (map f
          ((Rep.resTensorIso f (TensorPower.tensorPowObj A (n + 1)) A).inv ≫
            (fPow ⊗ₘ phi)) (n + 1 + 1)).hom
          ((cup H k (TensorPower.tensorPowObj A (n + 1)) A
            (n + 1) 1).hom
            (iteratedCupClassSucc A n (fun i => x i.castSucc) ⊗ₜ[k]
              x (Fin.last (n + 1)))) = _
      rw [hApply, ih]

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For x₁,x₂∈H¹(G,A) and q₂:P₂(A)≅A⊗A, L₁([x₁,x₂])=(q₂.inv)_*(x₁∪x₂). The ordinary cup lies in
H²(G,A⊗A), and the inverse comparison transports it to H²(G,P₂(A)). -/
theorem iteratedCupClassSucc_weightTwo
    (A : Rep k G) (x₁ x₂ : groupCohomology A 1) :
    iteratedCupClassSucc A 1 ![x₁, x₂] =
      (map (MonoidHom.id G) (TensorPower.tensorPowObjTwoIso A).inv 2).hom
        ((cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂)) := by
  rw [iteratedCupClassSucc_succ, iteratedCupClassSucc_zero]
  let f := (TensorPower.tensorPowObjOneIso A).inv
  change (cup G k (TensorPower.tensorPowObj A 1) A 1 1).hom
      ((map (MonoidHom.id G) f 1).hom x₁ ⊗ₜ[k] x₂) =
    (map (MonoidHom.id G) (TensorPower.tensorPowObjTwoIso A).inv 2).hom
      ((cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂))
  have hNat := cup_naturality (G := G) (k := k) f (𝟙 A) 1 1
  have hApply := congrArg (fun g => g.hom (x₁ ⊗ₜ[k] x₂)) hNat
  rw [TensorPower.tensorPowObjTwoIso_inv]
  simp [f] at hApply
  exact hApply.symm

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Let ψ₀:P₂(A)≅A⊗P₁(A) be the first-factor tensor comparison. For x₀,x₁∈H¹(G,A),
(ψ₀.hom)_*L₁([x₀,x₁])=x₀∪L₀([x₁]) in H²(G,A⊗P₁(A)). The tail uses the inverse one-factor
coefficient isomorphism. -/
theorem iteratedCupClassSucc_headTail_zero
    (A : Rep k G) (x₀ x₁ : groupCohomology A 1) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjHeadTailIso A 0).hom 2).hom
        (iteratedCupClassSucc A 1 ![x₀, x₁]) =
      cupOneAny A (TensorPower.tensorPowObj A 1) 1
        (x₀ ⊗ₜ[k] iteratedCupClassSucc A 0 ![x₁]) := by
  rw [iteratedCupClassSucc_weightTwo,
    iteratedCupClassSucc_zero]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  have hcoeff :
      (TensorPower.tensorPowObjTwoIso A).inv ≫
          (TensorPower.tensorPowObjHeadTailIso A 0).hom =
        𝟙 A ⊗ₘ (TensorPower.tensorPowObjOneIso A).inv := by
    unfold TensorPower.tensorPowObjHeadTailIso
    simp
  rw [hcoeff]
  have hnat := congrArg (fun f => f.hom (x₀ ⊗ₜ[k] x₁))
    (cup_naturality (G := G) (k := k)
      (𝟙 A) (TensorPower.tensorPowObjOneIso A).inv 1 1)
  rw [cupOneAny_one_eq]
  simpa using hnat

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0, x
indexed by {0,…,n+1}, and ψ_n:P_{n+2}(A)≅A⊗P_{n+1}(A), one has
(ψ_n.hom)_*L_{n+1}(x)=x₀∪L_n(x₁,…,x_{n+1}). The resulting degree is n+2 and the ordered tail has
n+1 inputs. -/
theorem iteratedCupClassSucc_headTail
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology A 1) :
    (map (MonoidHom.id G)
      (TensorPower.tensorPowObjHeadTailIso A n).hom (n + 2)).hom
        (iteratedCupClassSucc A (n + 1) x) =
      cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
        (x 0 ⊗ₜ[k]
          iteratedCupClassSucc A n (fun i => x i.succ)) := by
  induction n with
  | zero =>
      have hx : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      simpa using iteratedCupClassSucc_headTail_zero A (x 0) (x 1)
  | succ n ih =>
      let xPrefix : Fin (n + 2) → groupCohomology A 1 :=
        fun i => x i.castSucc
      let xTailPrefix : Fin (n + 1) → groupCohomology A 1 :=
        fun i => x i.succ.castSucc
      let xLast : groupCohomology A 1 := x (Fin.last (n + 2))
      let prefixClass := iteratedCupClassSucc A (n + 1) xPrefix
      let tailClass := iteratedCupClassSucc A n xTailPrefix
      have hnat := ConcreteCategory.congr_hom
        (cup_naturality (G := G) (k := k)
          (TensorPower.tensorPowObjHeadTailIso A n).hom (𝟙 A)
          (n + 2) 1) (prefixClass ⊗ₜ[k] xLast)
      rw [map_id] at hnat
      have hnat_apply :
          (map (MonoidHom.id G)
            ((TensorPower.tensorPowObjHeadTailIso A n).hom ⊗ₘ 𝟙 A)
            (n + 3)).hom
            ((cup G k (TensorPower.tensorPowObj A (n + 2)) A
              (n + 2) 1).hom (prefixClass ⊗ₜ[k] xLast)) =
          (cup G k
            (A ⊗ TensorPower.tensorPowObj A (n + 1)) A
            (n + 2) 1).hom
            ((map (MonoidHom.id G)
              (TensorPower.tensorPowObjHeadTailIso A n).hom
              (n + 2)).hom prefixClass ⊗ₜ[k] xLast) := by
        convert hnat using 1
        simp only [ConcreteCategory.comp_apply,
          ModuleCat.MonoidalCategory.tensorHom_tmul]
        rfl
      have ih' :
          (map (MonoidHom.id G)
            (TensorPower.tensorPowObjHeadTailIso A n).hom
            (n + 2)).hom prefixClass =
          cupOneAny A (TensorPower.tensorPowObj A (n + 1)) (n + 1)
            (x 0 ⊗ₜ[k] tailClass) := by
        convert ih xPrefix using 1
        all_goals rfl
      rw [iteratedCupClassSucc_succ]
      rw [TensorPower.tensorPowObjHeadTailIso_succ_hom]
      rw [map_id_comp]
      simp only [ConcreteCategory.comp_apply]
      change (map (MonoidHom.id G)
          (α_ A (TensorPower.tensorPowObj A (n + 1)) A).hom
          (n + 3)).hom
        ((map (MonoidHom.id G)
          ((TensorPower.tensorPowObjHeadTailIso A n).hom ⊗ₘ 𝟙 A)
          (n + 3)).hom
          ((cup G k (TensorPower.tensorPowObj A (n + 2)) A
            (n + 2) 1).hom (prefixClass ⊗ₜ[k] xLast))) = _
      rw [hnat_apply, ih']
      have hassoc := cupOneAny_assoc_right_one
        A (TensorPower.tensorPowObj A (n + 1)) A (n + 1)
        (x 0) tailClass xLast
      convert hassoc using 1
      all_goals rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0
and x₀,…,x_{n+1}, let ψ_n:P_{n+2}(A)≅A⊗P_{n+1}(A). The degree-(n+1) left-cup map by x₀, paired
through ψ_n.inv, sends L_n(x₁,…,x_{n+1}) to L_{n+1}(x). Equivalently (ψ_n.inv)_*(x₀∪L_n(tail
x))=L_{n+1}(x). -/
theorem cupOneClassMap_iteratedCupClassSucc_tail
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology A 1) :
    (cupOneClassMap (x 0)
      (TensorPower.tensorPowObjHeadTailIso A n).inv (n + 1)).hom
        (iteratedCupClassSucc A n (fun i => x i.succ)) =
      iteratedCupClassSucc A (n + 1) x := by
  rw [cupOneClassMap_apply]
  rw [← iteratedCupClassSucc_headTail]
  rw [← ConcreteCategory.comp_apply, ← map_id_comp]
  rw [Iso.hom_inv_id]
  change (map (MonoidHom.id G)
    (𝟙 (TensorPower.tensorPowObj A (n + 2))) (n + 2)).hom
      (iteratedCupClassSucc A (n + 1) x) = _
  rw [map_id]
  rfl

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For x₁,x₂∈H¹(G,A), if L₁([x₁,x₂])=0 in H²(G,P₂(A)), then x₁∪x₂=0 in H²(G,A⊗A). The canonical
isomorphism P₂(A)≅A⊗A recovers the binary cup from its tensor-power coefficient transport. -/
theorem cup_eq_zero_of_iteratedCupClassSucc_weightTwo_eq_zero
    (A : Rep k G) (x₁ x₂ : groupCohomology A 1)
    (hzero : iteratedCupClassSucc A 1 ![x₁, x₂] = 0) :
    (cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂) = 0 := by
  let raw : groupCohomology (A ⊗ A) 2 :=
    (cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂)
  change raw = 0
  rw [iteratedCupClassSucc_weightTwo] at hzero
  change (map (MonoidHom.id G)
    (TensorPower.tensorPowObjTwoIso A).inv 2).hom raw = 0 at hzero
  have hinj : Function.Injective
      (map (A := A ⊗ A) (B := TensorPower.tensorPowObj A 2)
        (MonoidHom.id G)
        (TensorPower.tensorPowObjTwoIso A).inv 2).hom := by
    apply (ModuleCat.mono_iff_injective _).mp
    change Mono ((groupCohomology.functor k G 2).map
      (TensorPower.tensorPowObjTwoIso A).inv)
    infer_instance
  apply hinj
  simpa only [map_zero] using hzero

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Let q₂:P₂(A)≅A⊗A, u∈H²(G,A⊗A), and x∈H¹(G,A). Then ((q₂.inv)_*u)∪x=(q₂.inv⊗id_A)_*(u∪x) in
H³(G,P₂(A)⊗A). The right-hand cup is formed first with coefficient (A⊗A)⊗A. -/
theorem cup_tensorPowObjTwoIso_inv_apply
    (A : Rep k G) (u : groupCohomology (A ⊗ A) 2)
    (x : groupCohomology A 1) :
    (cup G k (TensorPower.tensorPowObj A 2) A 2 1).hom
        ((map (MonoidHom.id G)
          (TensorPower.tensorPowObjTwoIso A).inv 2).hom u ⊗ₜ[k] x) =
      (map (MonoidHom.id G)
        ((TensorPower.tensorPowObjTwoIso A).inv ⊗ₘ 𝟙 A) 3).hom
        ((cup G k (A ⊗ A) A 2 1).hom (u ⊗ₜ[k] x)) := by
  let e₂ := (TensorPower.tensorPowObjTwoIso A).inv
  have hNat := cup_naturality (G := G) (k := k) e₂ (𝟙 A) 2 1
  have hApply := congrArg (fun g => g.hom (u ⊗ₜ[k] x)) hNat
  simp [e₂] at hApply
  exact hApply.symm

set_option backward.isDefEq.respectTransparency false in
private theorem cup_assoc_one_one_one_apply
    (A : Rep k G) (x₁ x₂ x₃ : groupCohomology A 1) :
    (map (MonoidHom.id G) (α_ A A A).hom 3).hom
        ((cup G k (A ⊗ A) A 2 1).hom
          (((cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂)) ⊗ₜ[k] x₃)) =
      (cup G k A (A ⊗ A) 1 2).hom
        (x₁ ⊗ₜ[k] (cup G k A A 1 1).hom (x₂ ⊗ₜ[k] x₃)) := by
  have h := cup_assoc_tmul G k A A A 1 1 1 x₁ x₂ x₃
  simp only [Nat.reduceAdd] at h
  change (map (MonoidHom.id G) (α_ A A A).hom 3).hom
      ((cup G k (A ⊗ A) A 2 1).hom
        (((cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂)) ⊗ₜ[k] x₃)) =
    (cup G k A (A ⊗ A) 1 2).hom
      (x₁ ⊗ₜ[k] (cup G k A A 1 1).hom (x₂ ⊗ₜ[k] x₃)) at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Let q₂:P₂(A)≅A⊗A and e₃:A⊗(A⊗A)≅P₃(A) be the right-cube comparison. For z∈H³(G,(A⊗A)⊗A),
(q₂.inv⊗id_A)_*z=(e₃.hom)_*((α_{A,A,A}.hom)_*z). Both sides lie in H³(G,P₃(A)). -/
theorem tensorPowObjThreeRightIso_map_assoc_apply
    (A : Rep k G) (z : groupCohomology ((A ⊗ A) ⊗ A) 3) :
    (map (MonoidHom.id G)
        ((TensorPower.tensorPowObjTwoIso A).inv ⊗ₘ 𝟙 A) 3).hom z =
      (map (MonoidHom.id G)
        (TensorPower.tensorPowObjThreeRightIso A).hom 3).hom
        ((map (MonoidHom.id G) (α_ A A A).hom 3).hom z) := by
  let e₂ := (TensorPower.tensorPowObjTwoIso A).inv
  have hCoeff :
      (α_ A A A).hom ≫
          (TensorPower.tensorPowObjThreeRightIso A).hom =
        e₂ ⊗ₘ 𝟙 A := by
    rw [TensorPower.tensorPowObjThreeRightIso_hom]
    simp [e₂]
  rw [← ConcreteCategory.comp_apply]
  rw [← map_id_comp]
  rw [hCoeff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. For x₁,x₂,x₃∈H¹(G,A) and e₃:A⊗(A⊗A)≅P₃(A), L₂([x₁,x₂,x₃])=(e₃.hom)_*(x₁∪(x₂∪x₃)) in
H³(G,P₃(A)). The inner cup has degree two and coefficient A⊗A, and the outer cup has degrees
(1,2). -/
theorem iteratedCupClassSucc_weightThree
    (A : Rep k G) (x₁ x₂ x₃ : groupCohomology A 1) :
    iteratedCupClassSucc A 2 ![x₁, x₂, x₃] =
      (map (MonoidHom.id G)
        (TensorPower.tensorPowObjThreeRightIso A).hom 3).hom
        ((cup G k A (A ⊗ A) 1 2).hom
          (x₁ ⊗ₜ[k] (cup G k A A 1 1).hom (x₂ ⊗ₜ[k] x₃))) := by
  rw [iteratedCupClassSucc_succ]
  change (cup G k (TensorPower.tensorPowObj A 2) A 2 1).hom
      (iteratedCupClassSucc A 1 ![x₁, x₂] ⊗ₜ[k] x₃) = _
  rw [iteratedCupClassSucc_weightTwo]
  let leftClass := (cup G k (A ⊗ A) A 2 1).hom
    (((cup G k A A 1 1).hom (x₁ ⊗ₜ[k] x₂)) ⊗ₜ[k] x₃)
  let rightClass := (cup G k A (A ⊗ A) 1 2).hom
    (x₁ ⊗ₜ[k] (cup G k A A 1 1).hom (x₂ ⊗ₜ[k] x₃))
  rw [cup_tensorPowObjTwoIso_inv_apply]
  have hAssoc : (map (MonoidHom.id G) (α_ A A A).hom 3).hom
      leftClass = rightClass :=
    cup_assoc_one_one_one_apply A x₁ x₂ x₃
  rw [tensorPowObjThreeRightIso_map_assoc_apply]
  rw [hAssoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0
and a tuple x₀,…,x_{n+1}, if x_n∪x_{n+1}=0 in H²(G,A⊗A), then L_{n+1}(x)=0 in
H^{n+2}(G,P_{n+2}(A)). The final two entries are adjacent in the retained input order. -/
theorem iteratedCupClassSucc_eq_zero_of_last_cup
    (A : Rep k G) (n : ℕ)
    (x : Fin (n + 2) → groupCohomology A 1)
    (hpair : (cup G k A A 1 1).hom
      (x ⟨n, by omega⟩ ⊗ₜ[k] x ⟨n + 1, by omega⟩) = 0) :
    iteratedCupClassSucc A (n + 1) x = 0 := by
  cases n with
  | zero =>
      have hpair₀ : (cup G k A A 1 1).hom
          (x 0 ⊗ₜ[k] x 1) = 0 := by
        simpa using hpair
      have hx : x = ![x 0, x 1] := by
        funext j
        fin_cases j <;> rfl
      rw [hx, iteratedCupClassSucc_weightTwo, hpair₀, map_zero]
  | succ m =>
      let u := iteratedCupClassSucc A m
        (fun j : Fin (m + 1) => x ⟨j.val, by omega⟩)
      let y := x ⟨m + 1, by omega⟩
      let z := x ⟨m + 2, by omega⟩
      have hpair' : (cup G k A A 1 1).hom (y ⊗ₜ[k] z) = 0 := by
        simpa only [y, z] using hpair
      have hAssoc := cup_assoc_tmul G k
        (TensorPower.tensorPowObj A (m + 1)) A A
        (m + 1) 1 1 u y z
      rw [hpair', TensorProduct.tmul_zero, map_zero] at hAssoc
      let leftClass :=
        (cup G k (TensorPower.tensorPowObj A (m + 1) ⊗ A) A
          ((m + 1) + 1) 1).hom
          ((cup G k (TensorPower.tensorPowObj A (m + 1)) A
            (m + 1) 1).hom (u ⊗ₜ[k] y) ⊗ₜ[k] z)
      have htransport :
          (HomologicalComplex.cochainHomologyIsoOfEq k
            (inhomogeneousCochains
              (TensorPower.tensorPowObj A (m + 1) ⊗ (A ⊗ A)))
            (Nat.add_assoc (m + 1) 1 1)).hom.hom
            ((map (MonoidHom.id G)
              (α_ (TensorPower.tensorPowObj A (m + 1)) A A).hom
              (((m + 1) + 1) + 1)).hom leftClass) = 0 := by
        dsimp only [leftClass]
        convert hAssoc using 1
      have hAssocZero :
          (map (MonoidHom.id G)
            (α_ (TensorPower.tensorPowObj A (m + 1)) A A).hom
            (((m + 1) + 1) + 1)).hom leftClass = 0 := by
        apply (ModuleCat.mono_iff_injective
          (HomologicalComplex.cochainHomologyIsoOfEq k
            (inhomogeneousCochains
              (TensorPower.tensorPowObj A (m + 1) ⊗ (A ⊗ A)))
            (Nat.add_assoc (m + 1) 1 1)).hom).mp inferInstance
        simpa only [map_zero] using htransport
      have hMapInjective : Function.Injective
          (map
            (A := (TensorPower.tensorPowObj A (m + 1) ⊗ A) ⊗ A)
            (B := TensorPower.tensorPowObj A (m + 1) ⊗ (A ⊗ A))
            (MonoidHom.id G)
            (α_ (TensorPower.tensorPowObj A (m + 1)) A A).hom
            (((m + 1) + 1) + 1)).hom := by
        let e := (groupCohomology.functor k G (((m + 1) + 1) + 1)).mapIso
          (α_ (TensorPower.tensorPowObj A (m + 1)) A A)
        have he : e.hom = map
            (A := (TensorPower.tensorPowObj A (m + 1) ⊗ A) ⊗ A)
            (B := TensorPower.tensorPowObj A (m + 1) ⊗ (A ⊗ A))
            (MonoidHom.id G)
            (α_ (TensorPower.tensorPowObj A (m + 1)) A A).hom
            (((m + 1) + 1) + 1) := rfl
        have hinj := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
        rw [he] at hinj
        exact hinj
      have hLeft : leftClass = 0 := by
        apply hMapInjective
        simpa only [map_zero] using hAssocZero
      rw [iteratedCupClassSucc_succ, iteratedCupClassSucc_succ]
      change leftClass = 0
      exact hLeft

/-- Let k be a commutative ring, G a group, and A a k-linear G-representation, in the given universe
u. Write P_m(A) for the canonical left-associated tensor power, with P₀=I and P_{m+1}=P_m⊗A, and
L_n(x)∈H^{n+1}(G,P_{n+1}(A)) for the ordered iterated cup of n+1 classes x_i∈H¹(G,A). For n≥0,
x₀,…,x_n, and an index i with i+1<n+1, if x_i∪x_{i+1}=0 in H²(G,A⊗A), then L_n(x)=0 in
H^{n+1}(G,P_{n+1}(A)). This requires a consecutive pair and introduces no permutation of the
tuple. -/
theorem iteratedCupClassSucc_eq_zero_of_adjacent_cup
    (A : Rep k G) :
    ∀ (n : ℕ) (x : Fin (n + 1) → groupCohomology A 1)
      (i : ℕ) (hi : i + 1 < n + 1),
      (cup G k A A 1 1).hom
          (x ⟨i, by omega⟩ ⊗ₜ[k] x ⟨i + 1, hi⟩) = 0 →
        iteratedCupClassSucc A n x = 0
  | 0, x, i, hi, hpair => by omega
  | n + 1, x, i, hi, hpair => by
      by_cases hprefix : i + 1 < n + 1
      · let xp : Fin (n + 1) → groupCohomology A 1 :=
          fun j => x j.castSucc
        have hp : (cup G k A A 1 1).hom
            (xp ⟨i, by omega⟩ ⊗ₜ[k] xp ⟨i + 1, hprefix⟩) = 0 := by
          exact hpair
        have hz := iteratedCupClassSucc_eq_zero_of_adjacent_cup
          A n xp i hprefix hp
        rw [iteratedCupClassSucc_succ, hz,
          TensorProduct.zero_tmul, map_zero]
        rfl
      · have hiEq : i = n := by omega
        subst i
        exact iteratedCupClassSucc_eq_zero_of_last_cup A n x hpair

end groupCohomology

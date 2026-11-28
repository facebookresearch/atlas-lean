/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarResolution
public import MathlibExt.Algebra.Homology.Hochschild.Maps
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Additive

/-!
# Algebra maps between two-sided bar complexes

Let k be a commutative ring, A and B unital associative k-algebras, and
g : A → B a unital k-algebra homomorphism. In bar degree n, g acts on
all n+2 ordered factors of A ⊗[k] A^{⊗(n+1)}. This map commutes with
each adjacent multiplication and therefore with the alternating
bar boundary.

Write E_A = A ⊗[k] Aᵐᵒᵖ and E_B = B ⊗[k] Bᵐᵒᵖ. The two outer
factors carry the left E_A-action (u ⊗ vᵐᵒᵖ) • w = u w v.
The degree maps intertwine this action along E(g) = g ⊗ gᵐᵒᵖ and
give a map to the B-bar complex restricted to E_A. On the augmentation
targets the map is g, so Res(ε_B) Φ_g = g[0] ε_A.

Reference: J.-L. Loday, Cyclic Homology, §1.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] {A B : Type v} [Ring A] [Ring B]
  [Algebra k A] [Algebra k B] (g : A →ₐ[k] B)

/-- For a unital homomorphism g : A → B of associative algebras over a
commutative ring k, the induced enveloping-algebra homomorphism is
E(g) = g ⊗ gᵐᵒᵖ : A ⊗[k] Aᵐᵒᵖ → B ⊗[k] Bᵐᵒᵖ.
It sends a ⊗ bᵐᵒᵖ to g(a) ⊗ g(b)ᵐᵒᵖ. -/
def envelopingAlgebraMap : EnvelopingAlgebra k A →ₐ[k] EnvelopingAlgebra k B :=
  Algebra.TensorProduct.map g g.op

/-- For a unital k-algebra homomorphism g : A → B, with k commutative
and A,B associative, the degree-n bar map is the k-linear map
Φ_{g,n} = g ⊗ g^{⊗(n+1)} from
A ⊗[k] A^{⊗(n+1)} to B ⊗[k] B^{⊗(n+1)}. -/
def barAlgebraLevelMap (n : ℕ) :
    A ⊗[k] TensorPower k (n + 1) A →ₗ[k] B ⊗[k] TensorPower k (n + 1) B :=
  ModuleCat.Algebra.Hochschild.linearMap g.toNonUnitalAlgHom g.toLinearMap (n + 1)

/-- For a unital homomorphism g : A → B of associative k-algebras over
a commutative ring k, the degree-n bar map has the value
Φ_{g,n}(a_0 ⊗ tprod(a)) =
g(a_0) ⊗ tprod(j ↦ g(a_j)). The order of all n+2 factors is retained. -/
theorem barAlgebraLevelMap_tprod (n : ℕ) (a₀ : A) (a : Fin (n + 1) → A) :
    barAlgebraLevelMap k g n (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      g a₀ ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j)) :=
  ModuleCat.Algebra.Hochschild.linearMap_tprod g.toNonUnitalAlgHom g.toLinearMap (n + 1) a₀ a

/-- For a unital homomorphism g : A → B of associative k-algebras over
a commutative ring k, the bar map sends the word
1 ⊗ a_1 ⊗ ⋯ ⊗ a_n ⊗ 1 to
1 ⊗ g(a_1) ⊗ ⋯ ⊗ g(a_n) ⊗ 1. -/
theorem barAlgebraLevelMap_unit_word (n : ℕ) (a : Fin n → A) :
    barAlgebraLevelMap k g n ((1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)) =
      (1 : B) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc (fun j => g (a j)) 1) := by
  rw [barAlgebraLevelMap_tprod, map_one]
  apply congrArg (fun z => (1 : B) ⊗ₜ[k] z)
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  refine Fin.lastCases ?_ (fun q => ?_) j
  · simp only [Fin.snoc_last, map_one]
  · simp only [Fin.snoc_castSucc]

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
let κ_A : A ⊗[k] A^{⊗(n+1)} ≃ A^{⊗(n+2)} be the
ordered-word identification, and define κ_B similarly. Then
κ_B Φ_{g,n} = g^{⊗(n+2)} κ_A. -/
theorem barAlgebraLevelMap_cons (n : ℕ) (z : A ⊗[k] TensorPower k (n + 1) A) :
    TensorPower.consEquiv k B (n + 1) (barAlgebraLevelMap k g n z) =
      PiTensorProduct.map (fun _ : Fin (n + 2) => g.toLinearMap)
        (TensorPower.consEquiv k A (n + 1) z) := by
  have h := DFunLike.congr_fun (TensorPower.consEquiv_naturality g.toLinearMap (n + 1)) z
  change TensorPower.consEquiv k B (n + 1) (barAlgebraLevelMap k g n z) =
    PiTensorProduct.map (fun _ : Fin (n + 2) => g.toLinearMap)
      (TensorPower.consEquiv k A (n + 1) z) at h
  exact h

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
each adjacent-multiplication face δ_i : P_{n+1} → P_n satisfies
Φ_{g,n} δ_i^A = δ_i^B Φ_{g,n+1}, for 0 ≤ i ≤ n+1.
The equality follows from g(ab) = g(a)g(b). -/
@[reassoc]
theorem barAlgebraLevelMap_face (n : ℕ) (i : Fin (n + 2)) :
    NonUnital.regularFace k A (n + 1) i.castSucc ≫ ModuleCat.ofHom (barAlgebraLevelMap k g n) =
      ModuleCat.ofHom (barAlgebraLevelMap k g (n + 1)) ≫
        NonUnital.regularFace k B (n + 1) i.castSucc := by
  apply ModuleCat.hom_ext
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro a₀ a
  apply (TensorPower.consEquiv k B (n + 1)).injective
  change TensorPower.consEquiv k B (n + 1)
    (barAlgebraLevelMap k g n
      ((NonUnital.regularFace k A (n + 1) i.castSucc).hom
        (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    TensorPower.consEquiv k B (n + 1)
      ((NonUnital.regularFace k B (n + 1) i.castSucc).hom
        (barAlgebraLevelMap k g (n + 1) (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)))
  rw [barAlgebraLevelMap_cons, NonUnital.regularFace_cons_tprod,
    PiTensorProduct.map_tprod, barAlgebraLevelMap_tprod,
    NonUnital.regularFace_cons_tprod]
  apply congrArg (PiTensorProduct.tprod k)
  funext j
  let wA : Fin (n + 3) → A := Fin.cons a₀ a
  let wB : Fin (n + 3) → B := Fin.cons (g a₀) (fun j : Fin (n + 2) => g (a j))
  have hc : (fun j => g (wA j)) = wB := Fin.comp_cons (fun x => g x) a₀ a
  simp only [hochschildMulAdjacent]
  split_ifs with hj
  · subst j
    change g (wA i.castSucc * a i) = wB i.castSucc * g (a i)
    exact (g.map_mul _ _).trans (congrArg (fun x => x * g (a i)) (congrFun hc i.castSucc))
  · change g (wA (i.succ.succAbove j)) = wB (i.succ.succAbove j)
    exact congrFun hc (i.succ.succAbove j)

/-- For a commutative ring k and an associative unital k-algebra T,
the k-linear boundary map P_{n+1}(T) → P_n(T) is the sum
∑_{i=0}^{n+1} (−1)^i δ_i of adjacent multiplications. -/
private theorem underlyingBar_d_hom (T : Type v) [Ring T] [Algebra k T] (n : ℕ) :
    ((underlyingBar k T).d (n + 1) n).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (NonUnital.regularFace k T (n + 1) i.castSucc).hom := by
  have h := congrArg ModuleCat.Hom.hom (underlyingBar_d k T n)
  have hs : (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        NonUnital.regularFace k T (n + 1) i.castSucc).hom =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (NonUnital.regularFace k T (n + 1) i.castSucc).hom :=
    (ModuleCat.hom_sum (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val •
      NonUnital.regularFace k T (n + 1) i.castSucc) Finset.univ).trans
        (Finset.sum_congr rfl (fun i _ => ModuleCat.hom_zsmul _ _))
  exact h.trans hs

/-- For a unital homomorphism g : A → B of associative algebras over
a commutative ring k, the maps g ⊗ g^{⊗(n+1)} form a chain map
between the adjacent-product bar complexes over k:
Φ_{g,n} d_A = d_B Φ_{g,n+1}. -/
def underlyingBarAlgebraMap : underlyingBar k A ⟶ underlyingBar k B :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (barAlgebraLevelMap k g n)) (by
    intro n
    change ModuleCat.ofHom (barAlgebraLevelMap k g (n + 1)) ≫ (underlyingBar k B).d (n + 1) n =
      (underlyingBar k A).d (n + 1) n ≫ ModuleCat.ofHom (barAlgebraLevelMap k g n)
    let fA (i : Fin (n + 2)) : A ⊗[k] TensorPower k (n + 2) A →ₗ[k]
        A ⊗[k] TensorPower k (n + 1) A := (NonUnital.regularFace k A (n + 1) i.castSucc).hom
    let fB (i : Fin (n + 2)) : B ⊗[k] TensorPower k (n + 2) B →ₗ[k]
        B ⊗[k] TensorPower k (n + 1) B := (NonUnital.regularFace k B (n + 1) i.castSucc).hom
    have hdA : ((underlyingBar k A).d (n + 1) n).hom =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • fA i := underlyingBar_d_hom k A n
    have hdB : ((underlyingBar k B).d (n + 1) n).hom =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • fB i := underlyingBar_d_hom k B n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((underlyingBar k B).d (n + 1) n).hom (barAlgebraLevelMap k g (n + 1) z) =
      barAlgebraLevelMap k g n (((underlyingBar k A).d (n + 1) n).hom z)
    rw [hdA, hdB]
    change (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • fB i) (barAlgebraLevelMap k g (n + 1) z) =
      barAlgebraLevelMap k g n ((∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • fA i) z)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    have h := ConcreteCategory.congr_hom (barAlgebraLevelMap_face k g n i) z
    change barAlgebraLevelMap k g n (fA i z) = fB i (barAlgebraLevelMap k g (n + 1) z) at h
    exact congrArg (fun y => (-1 : ℤ) ^ i.val • y) h.symm)

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
the degree-n bar map is equivariant along E(g) = g ⊗ gᵐᵒᵖ.
For e ∈ E_A and z ∈ P_n(A),
Φ_{g,n}(e • z) = E(g)(e) • Φ_{g,n}(z),
where the enveloping action multiplies the two outer factors. -/
theorem barAlgebraLevelMap_outer (n : ℕ) (e : EnvelopingAlgebra k A)
    (z : A ⊗[k] TensorPower k (n + 1) A) :
    barAlgebraLevelMap k g n (TensorPower.outerRepresentation k A n e z) =
      TensorPower.outerRepresentation k B n (envelopingAlgebraMap k g e)
        (barAlgebraLevelMap k g n z) := by
  induction e using TensorProduct.inductionOn with
  | tmul l r =>
      let L := (barAlgebraLevelMap k g n).comp
        (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] r))
      let R := (TensorPower.outerRepresentation k B n
        (envelopingAlgebraMap k g (l ⊗ₜ[k] r))).comp (barAlgebraLevelMap k g n)
      have h : L = R := by
        apply ModuleCat.Algebra.Hochschild.tensorPower_ext
        intro a₀ a
        have hA := TensorPower.outerModule_tprod k A n l r.unop a₀ a
        change TensorPower.outerRepresentation k A n (l ⊗ₜ[k] MulOpposite.op r.unop)
          (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) = _ at hA
        rw [MulOpposite.op_unop] at hA
        change barAlgebraLevelMap k g n
          (TensorPower.outerRepresentation k A n (l ⊗ₜ[k] r)
            (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)) =
          TensorPower.outerRepresentation k B n (envelopingAlgebraMap k g (l ⊗ₜ[k] r))
            (barAlgebraLevelMap k g n (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a))
        rw [hA, barAlgebraLevelMap_tprod, barAlgebraLevelMap_tprod]
        have hr : g.op r = MulOpposite.op (g r.unop) := rfl
        rw [envelopingAlgebraMap, Algebra.TensorProduct.map_tmul, hr]
        have hB := TensorPower.outerModule_tprod k B n (g l) (g r.unop) (g a₀)
          (fun j => g (a j))
        change TensorPower.outerRepresentation k B n (g l ⊗ₜ[k] MulOpposite.op (g r.unop))
          (g a₀ ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j))) = _ at hB
        rw [hB]
        simp only [map_mul]
        congr 1
        apply congrArg (PiTensorProduct.tprod k)
        funext j
        refine Fin.lastCases ?_ (fun q => ?_) j
        · simp only [Fin.snoc_last, map_mul]
        · simp only [Fin.snoc_castSucc]
          rfl
      exact DFunLike.congr_fun h z
  | add e e' he he' =>
      simp only [map_add, LinearMap.add_apply, he, he']

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
the degree maps Φ_{g,n} define a chain map of E_A-modules from the
A-bar complex to the B-bar complex restricted along
E(g) : E_A → E_B. Each component applies g to every ordered factor. -/
def envelopingBarAlgebraMap :
    envelopingBar k A ⟶
      ((ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).mapHomologicalComplex
        (.down ℕ)).obj (envelopingBar k B) :=
  ChainComplex.ofHom (fun n => by
    let X := (envelopingBar k A).X n
    let Y := (ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).obj
      ((envelopingBar k B).X n)
    let h : X →ₗ[EnvelopingAlgebra k A] Y :=
      { toFun := fun z => barAlgebraLevelMap k g n z
        map_add' := (barAlgebraLevelMap k g n).map_add
        map_smul' := by
          intro e z
          change barAlgebraLevelMap k g n (TensorPower.outerRepresentation k A n e z) =
            TensorPower.outerRepresentation k B n (envelopingAlgebraMap k g e)
              (barAlgebraLevelMap k g n z)
          exact barAlgebraLevelMap_outer k g n e z }
    exact { hom' := h }) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((envelopingBar k B).d (n + 1) n).hom (barAlgebraLevelMap k g (n + 1) z) =
      barAlgebraLevelMap k g n (((envelopingBar k A).d (n + 1) n).hom z)
    have hA : ((envelopingBar k A).d (n + 1) n).hom z =
        ((underlyingBar k A).d (n + 1) n).hom z := envelopingBar_d_apply k A n z
    have hB : ((envelopingBar k B).d (n + 1) n).hom (barAlgebraLevelMap k g (n + 1) z) =
        ((underlyingBar k B).d (n + 1) n).hom (barAlgebraLevelMap k g (n + 1) z) :=
      envelopingBar_d_apply k B n (barAlgebraLevelMap k g (n + 1) z)
    have h := ConcreteCategory.congr_hom ((underlyingBarAlgebraMap k g).comm (n + 1) n) z
    change ((underlyingBar k B).d (n + 1) n).hom (barAlgebraLevelMap k g (n + 1) z) =
      barAlgebraLevelMap k g n (((underlyingBar k A).d (n + 1) n).hom z) at h
    exact hB.trans (h.trans (congrArg (barAlgebraLevelMap k g n) hA.symm)))

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
g induces an E_A-linear map from the lifted regular module A to the
lifted regular module B restricted along E(g). The regular action is
(u ⊗ vᵐᵒᵖ) • a = uav, and the map sends the lift of a to the lift of g(a). -/
def regularEnvelopingTargetAlgebraMap : regularEnvelopingTarget k A ⟶
    (ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).obj
      (regularEnvelopingTarget k B) :=
  by
    let X := regularEnvelopingTarget k A
    let Y := (ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).obj
      (regularEnvelopingTarget k B)
    let h : X →ₗ[EnvelopingAlgebra k A] Y :=
      { toFun := fun a => ULift.up (g a.down)
        map_add' := by intro a b; apply ULift.ext; exact g.map_add a.down b.down
        map_smul' := by
          intro e a
          apply ULift.ext
          change g (regularEnvelopingAction k A e a.down) =
            regularEnvelopingAction k B (envelopingAlgebraMap k g e) (g a.down)
          induction e using TensorProduct.inductionOn with
          | tmul l r =>
              have hr : g.op r = MulOpposite.op (g r.unop) := rfl
              rw [envelopingAlgebraMap, Algebra.TensorProduct.map_tmul, hr]
              simp only [regularEnvelopingAction, AlgHom.mulLeftRight_apply, map_mul,
                  MulOpposite.unop_op]
          | add e e' he he' => simp only [map_add, LinearMap.add_apply, he, he'] }
    exact { hom' := h }

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
the induced map of the regular enveloping modules extends to the
complexes concentrated in degree zero. Its degree-zero component is
g on the lifted carriers, with the B-target restricted along E(g). -/
def envelopingBarAlgebraSingleTargetMap :
    (ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).obj (regularEnvelopingTarget k A) ⟶
      ((ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).mapHomologicalComplex
        (.down ℕ)).obj
        ((ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k B))).obj (regularEnvelopingTarget k
            B)) :=
  (ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).map
      (regularEnvelopingTargetAlgebraMap k g) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom) (.down ℕ) 0).inv.app
        (regularEnvelopingTarget k B)

/-- For a unital k-algebra homomorphism g : A → B over commutative k,
the enveloping bar chain map covers g on the regular augmentation
targets. The square is
Res(ε_B) Φ_g = g[0] ε_A,
where Res restricts scalars along E(g) and ε_A,ε_B multiply the
two degree-zero outer factors. -/
@[reassoc]
theorem envelopingBarAlgebraMap_augmentation :
    envelopingBarAlgebraMap k g ≫
      ((ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom).mapHomologicalComplex
        (.down ℕ)).map (envelopingBarAugmentationMap k B) =
      envelopingBarAugmentationMap k A ≫ envelopingBarAlgebraSingleTargetMap k g := by
  let F := ModuleCat.restrictScalars (envelopingAlgebraMap k g).toRingHom
  let S := HomologicalComplex.singleMapHomologicalComplex F (.down ℕ) 0
  apply (cancel_mono (S.hom.app (regularEnvelopingTarget k B))).1
  have htarget : envelopingBarAlgebraSingleTargetMap k g ≫
      S.hom.app (regularEnvelopingTarget k B) =
    (ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).map
      (regularEnvelopingTargetAlgebraMap k g) := by
    change ((ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).map
      (regularEnvelopingTargetAlgebraMap k g) ≫ S.inv.app (regularEnvelopingTarget k B)) ≫
        S.hom.app (regularEnvelopingTarget k B) = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h => (ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).map
        (regularEnvelopingTargetAlgebraMap k g) ≫ h)
          (S.app (regularEnvelopingTarget k B)).inv_hom_id).trans (Category.comp_id _))
  have hright : (envelopingBarAugmentationMap k A ≫ envelopingBarAlgebraSingleTargetMap k g) ≫
      S.hom.app (regularEnvelopingTarget k B) =
    envelopingBarAugmentationMap k A ≫
      (ChainComplex.single₀ (ModuleCat (EnvelopingAlgebra k A))).map
        (regularEnvelopingTargetAlgebraMap k g) :=
    (Category.assoc _ _ _).trans (congrArg (fun h => envelopingBarAugmentationMap k A ≫ h) htarget)
  rw [hright]
  let L : A ⊗[k] TensorPower k 1 A →ₗ[k] ULift.{max u v} B :=
    (ULift.moduleEquiv.symm.toLinearMap : B →ₗ[k] ULift.{max u v} B).comp
      ((underlyingBarAugmentationLinear k B).comp (barAlgebraLevelMap k g 0))
  let R : A ⊗[k] TensorPower k 1 A →ₗ[k] ULift.{max u v} B :=
    (ULift.moduleEquiv.symm.toLinearMap : B →ₗ[k] ULift.{max u v} B).comp
      (g.toLinearMap.comp (underlyingBarAugmentationLinear k A))
  have hvalue : L = R := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro a₀ a
    change ULift.up (underlyingBarAugmentationLinear k B
      (barAlgebraLevelMap k g 0 (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a))) =
        ULift.up (g (underlyingBarAugmentationLinear k A (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)))
    apply ULift.ext
    change underlyingBarAugmentationLinear k B
        (barAlgebraLevelMap k g 0 (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      g (underlyingBarAugmentationLinear k A (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a))
    have hm := barAlgebraLevelMap_tprod k g 0 a₀ a
    have hB := underlyingBarAugmentationLinear_tprod k B (g a₀) (fun j => g (a j))
    have hA := underlyingBarAugmentationLinear_tprod k A a₀ a
    exact (congrArg (underlyingBarAugmentationLinear k B) hm).trans
      (hB.trans ((g.map_mul a₀ (a 0)).symm.trans (congrArg g hA.symm)))
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change L z = R z
  exact DFunLike.congr_fun hvalue z

end ModuleCat.Algebra.Hochschild.AdjacentBar

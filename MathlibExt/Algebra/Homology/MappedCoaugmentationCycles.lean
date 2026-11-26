/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RepresentationTheory.Homological.ContCohomology.NativeZeroCochainClasses
public import MathlibExt.CategoryTheory.Abelian.CoaugmentationCycles

/-!
# Classes of mapped coaugmentation cycles

For a profinite group G in v and a topological integer representation X with coefficient carrier
W=max(v,w), invariant coefficients identify with continuous cohomology in degree zero. The
zero-cycle inclusion sends an invariant vector to its constant homogeneous zero-cochain.

Let F forget topological integer modules to abelian groups. A coefficient short complex T
identified with F(C^*_{hom}(G,X).sc(0)), and a cycle map p from F(X^G), have the same
degree-zero class whenever their middle-vector map is the constant invariant inclusion. The
class comparison includes the short-complex isomorphism and the canonical homology comparison
for F.

The comparison, cycle map, and vector identity form coefficient-cycle data. Pointwise constancy
of the represented vector constructs these data and determines the resulting class map.
-/

/-!
## The class of a constant invariant cycle

The map p:F(X^G)→Z(T), followed by the class projection, the induced map of e:T≅F(S), and the
homology comparison H(F(S))≅F(H(S)), equals the inverse degree-zero invariants isomorphism under
F.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
ℤ-modules to abelian groups in W. Let T be a short complex of abelian groups in W, e:T≅F(S), and
p:F(I)→Z(T). Assume p≫i_T≫e₂=F(c_X≫i_0), where c_X:I→Z⁰(K) is the constant invariant cycle
inclusion. For ζ_X:H⁰_cont(G,X)≅I and h_F:H(F(S))≅F(H(S)), one has
p≫π_T≫H(e).hom≫h_F.hom=F(ζ_X.inv). -/
theorem nativeZeroShortComplexClass_of_constant_cycle
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w})
    (e : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w})
    (p : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles)
    (hc : p ≫ T.iCycles ≫ e.hom.τ₂ =
      discreteCoefficientForget.{max v w}.map
        (zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0)) :
    p ≫ T.homologyπ ≫ ShortComplex.homologyMap e.hom ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso discreteCoefficientForget.{max v w}).hom =
      discreteCoefficientForget.{max v w}.map (zeroIso X).inv := by
  let U := discreteCoefficientForget.{max v w}
  let S := (TopRep.homogeneousCochains X).sc 0
  let c := zeroCycleInclusion G X
  let z := (S.mapCyclesIso U).inv
  have hz : z ≫ (S.map U).iCycles = U.map S.iCycles := by
    exact (congrArg (fun q => z ≫ q) (S.mapCyclesIso_hom_iCycles U).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ U.map S.iCycles) (S.mapCyclesIso U).inv_hom_id).trans
          (Category.id_comp _)))
  have hcycle : p ≫ ShortComplex.cyclesMap e.hom = U.map c ≫ z := by
    apply (cancel_mono (S.map U).iCycles).mp
    have hn := ShortComplex.cyclesMap_i e.hom
    have hr : (U.map c ≫ z) ≫ (S.map U).iCycles = U.map (c ≫ S.iCycles) :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => U.map c ≫ q) hz).trans (U.map_comp _ _).symm)
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun q => p ≫ q) hn).trans (hc.trans hr.symm))
  have hπ := ShortComplex.homologyπ_naturality e.hom
  have hforget := discreteForgetZeroCycle_class G X (U.obj ((TopRep.invariantsFunctor ℤ G).obj X)) (U.map c)
  have hπ' : p ≫ T.homologyπ ≫ ShortComplex.homologyMap e.hom =
      U.map c ≫ z ≫ (S.map U).homologyπ := by
    rw [hπ, ← Category.assoc, hcycle, Category.assoc]
  have hforget' : (U.map c ≫ z ≫ (S.map U).homologyπ) ≫ (S.mapHomologyIso U).hom =
      U.map c ≫ U.map (π X 0) := by
    exact (Category.assoc _ _ _).trans hforget
  exact (congrArg (fun q => q ≫ (S.mapHomologyIso U).hom) hπ').trans
    (hforget'.trans ((U.map_comp _ _).symm.trans (congrArg U.map (zeroCycleInclusion_projection G X))))

end ContinuousCohomology
end

/-!
## Coefficient zero-cycle data

The data consist of the short-complex comparison e, the invariant cycle map p, and the equation
identifying its included vector with the constant invariant zero-cochain. Their degree-zero
class formula follows from these three components.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
ℤ-modules to abelian groups in W. For a short complex T of abelian groups, the data are
e:T≅F(S), p:F(I)→Z(T), and the vector identity p≫i_T≫e₂=F(c_X≫i_0). Here c_X includes invariant
coefficients as zero cycles of K, and i_0 includes them into K⁰. -/
structure NativeZeroCoefficientCycle (G : ProfiniteGrp.{v})
    (X : TopRep.{max v w, 0, v} ℤ G) (T : ShortComplex AddCommGrpCat.{max v w}) where
  /-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
  carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
  ℤ-modules to abelian groups in W. For a short complex T of abelian groups in W and
  coefficient-cycle data on it, the comparison is an isomorphism e:T≅F(S) of short complexes of
  abelian groups. Its middle component transports the coefficient vector into the forgotten
  homogeneous zero-cochain term. -/
  comparison : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w}
  /-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
  carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
  ℤ-modules to abelian groups in W. For a short complex T in abelian groups, the cycle component
  p:F(I)→Z(T) is an additive morphism from invariant coefficients to its cycles. The vector
  component identifies p≫i_T after the middle comparison with the constant invariant
  coaugmentation. -/
  cycle : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles
  /-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
  carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
  ℤ-modules to abelian groups in W. Let T be a short complex of abelian groups in W, e:T≅F(S), and
  p:F(I)→Z(T). The vector law is p≫i_T≫e₂=F(c_X≫i_0) as maps F(I)→F(K⁰). Thus each invariant
  coefficient is represented by its constant homogeneous zero-cochain after the complex
  comparison. -/
  vector : cycle ≫ T.iCycles ≫ comparison.hom.τ₂ =
    discreteCoefficientForget.{max v w}.map
      (zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0)

/-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
ℤ-modules to abelian groups in W. For a short complex T of abelian groups in W and
coefficient-cycle data d on T, let e=d.comparison and p=d.cycle. Then
p≫π_T≫H(e).hom≫h_F.hom=F(ζ_X.inv), with ζ_X:H⁰_cont(G,X)≅I and h_F:H(F(S))≅F(H(S)). The vector
law determines this full class map. -/
theorem NativeZeroCoefficientCycle.class_eq
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w}) (d : NativeZeroCoefficientCycle G X T) :
    d.cycle ≫ T.homologyπ ≫ ShortComplex.homologyMap d.comparison.hom ≫
      (((TopRep.homogeneousCochains X).sc 0).mapHomologyIso discreteCoefficientForget.{max v w}).hom =
      discreteCoefficientForget.{max v w}.map (zeroIso X).inv :=
  nativeZeroShortComplexClass_of_constant_cycle G X T d.comparison d.cycle d.vector

end ContinuousCohomology
end

/-!
## Values of the invariant zero-cycle inclusion

For a ring R with a topology and a topological R-representation of a profinite group, every
invariant vector maps to the constant homogeneous zero-cochain with that same value at each
group element.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe r v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology
variable {R : Type r} [Ring R] [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Let R be a ring with a topology in universe r, G a profinite group in v, and X a topological
R-representation with coefficient carrier max(v,w). For x∈X^G and g∈G, the cochain obtained by
including its zero cycle into C⁰_{hom}(G,X) has value x at g. -/
theorem zeroCycleInclusion_constant
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, r, v} R G)
    (x : X.ρ.invariants) (g : G) :
    (((zeroCycleInclusion G X ≫ (TopRep.homogeneousCochains X).iCycles 0) x).val g) = x.val := by
  unfold zeroCycleInclusion
  let c : (TopRep.invariantsFunctor R G).obj X ⟶
      (show TopModuleCat.{max v w} R from
        @TopModuleCat.of R _ _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker)
          _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker.module) _ _ _) :=
    (TopModuleCat.ofIso (ContinuousCohomology.d₀kerIso X)).inv
  let z := ContinuousCohomology.cocycles₀Iso X
  have hz : z.inv ≫ (TopRep.homogeneousCochains X).iCycles 0 =
      TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 0 1) := by
    exact (congrArg (fun q => z.inv ≫ q) (homogeneousZeroCocycles_projection.{r, v, w} X).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ TopModuleCat.kerι ((TopRep.homogeneousCochains X).d 0 1)) z.inv_hom_id).trans
          (Category.id_comp _)))
  have h := congrArg
    (fun q : (show TopModuleCat.{max v w} R from
        @TopModuleCat.of R _ _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker)
          _ (((TopRep.homogeneousCochains X).d 0 1).hom.ker.module) _ _ _) ⟶
        (TopRep.homogeneousCochains X).X 0 => ((c ≫ q) x).val g) hz
  exact h.trans (homogeneousZeroIso_inverse_constant.{r, v, w} X x g)

end ContinuousCohomology
end

/-!
## Constructing coefficient data from pointwise vectors

If the included vector of p, transported by the middle component of e, has value x at every g∈G
for each invariant x, this pointwise condition supplies the coefficient-cycle vector identity.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

/-- Let G be a profinite group in universe v and X a topological ℤ-representation with coefficient
carrier W=max(v,w). Put K=C^*_{hom}(G,X), S=K.sc(0), I=X^G, and let F forget topological
ℤ-modules to abelian groups in W. Let T be a short complex of abelian groups in W, e:T≅F(S), and
p:F(I)→Z(T). Suppose for every x∈F(I) and g∈G, the cochain vector e₂(i_T(p(x))) has value x at
g. This constructs coefficient-cycle data with comparison e and cycle p; its vector identity is
equality with F(c_X≫i_0). -/
def nativeZeroCoefficientCycleOfVector
    (G : ProfiniteGrp.{v}) (X : TopRep.{max v w, 0, v} ℤ G)
    (T : ShortComplex AddCommGrpCat.{max v w})
    (e : T ≅ ((TopRep.homogeneousCochains X).sc 0).map discreteCoefficientForget.{max v w})
    (p : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X) ⟶ T.cycles)
    (hv : ∀ (x : discreteCoefficientForget.{max v w}.obj ((TopRep.invariantsFunctor ℤ G).obj X)) (g : G), ((p ≫ T.iCycles ≫ e.hom.τ₂) x).val g = x.val) :
    NativeZeroCoefficientCycle G X T where
  comparison := e
  cycle := p
  vector := by
    apply ConcreteCategory.ext
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    exact (hv x g).trans (zeroCycleInclusion_constant G X x g).symm

end ContinuousCohomology
end

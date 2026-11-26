/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleTensorCoefficients
public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricClosureComparison
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientCupProduct
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
# Tensor stalks, point maps and Galois coefficients

For a scheme X in universe u and c = max(u, w), the point-stalk map on
the integer tensor presheaf is natural under morphisms of points.
A point morphism h : p → q induces a stalk map q* → p*, and sends
a germ at q to the germ at p at the corresponding fiber coordinate.
The sheafified tensor comparison has the same naturality.

For a separable closure Ω/k of fields in universe u, these comparisons
are equivariant for G = Gal(Ω/k). The stalk of F ⊗_sheaf H is naturally
the diagonal tensor E(F) ⊗[ℤ] E(H) in discrete G-modules and in
topological ℤ-representations. A pure tensor section at a geometric
lift z maps to germ_z(a) ⊗ germ_z(b).
The inverse Galois sheaf has the corresponding equivariant-function value,
and the tensor comparison commutes with embeddings Ω → Ψ into any
separably closed k-field Ψ in universe u.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Let X be a scheme in universe u, c = max(u, w), p, q points of
its small étale site, and h : p → q a point morphism.
For an AddCommGrpCat c-valued presheaf P, U ∈ Etale(X) and
x ∈ fiber_q(U), the induced stalk map h* : P_q → P_p satisfies
h*(germ_q(U, x)) = germ_p(U, h_U(x)) as maps from P(U).
The point coordinate map h_U goes from fiber_q(U) to fiber_p(U). -/
theorem pointHom_presheafFiber_germ (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) (U : X.Etale) (x : q.fiber.obj U) :
    q.toPresheafFiber U x P ≫ h.presheafFiber.app P =
      p.toPresheafFiber U (h.hom.app U x) P := by
  exact q.toPresheafFiber_presheafFiberDesc
    (fun V y => p.toPresheafFiber V (h.hom.app V y) P)
    (by
      intro V Z f y
      refine (p.toPresheafFiber_w f (h.hom.app V y) P).trans ?_
      exact congrArg (fun z => p.toPresheafFiber Z z P)
        (h.hom.naturality_apply f y).symm)
    U x

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u, c = max(u, w), h : p → q a
morphism of points of its small étale site, and F, H presheaves of
abelian groups in universe c. For the integer tensor presheaf, the
stalk tensor maps satisfy
τ_p ∘ h*_(F⊗H) = (h*_F ⊗ h*_H) ∘ τ_q,
where each h* goes from the q-stalk to the p-stalk. -/
theorem smallEtalePointTensorStalkMap_point_naturality (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (F G : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w}) :
    h.presheafFiber.app (smallEtaleTensorPresheaf.{u, w} X F G) ≫
        smallEtalePointTensorStalkMap.{u, w} X p F G =
      smallEtalePointTensorStalkMap.{u, w} X q F G ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (h.presheafFiber.app F).hom.toIntLinearMap
          (h.presheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom := by
  apply q.presheafFiber_hom_ext
  intro U x
  have ht := pointHom_presheafFiber_germ X h (smallEtaleTensorPresheaf.{u, w} X F G) U x
  have hp : p.toPresheafFiber U (h.hom.app U x) (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X p F G =
      AddCommGrpCat.ofHom (TensorProduct.map
        (p.toPresheafFiber U (h.hom.app U x) F).hom.toIntLinearMap
        (p.toPresheafFiber U (h.hom.app U x) G).hom.toIntLinearMap).toAddMonoidHom :=
    p.toPresheafFiber_presheafFiberDesc _ _ U (h.hom.app U x)
  have hq : q.toPresheafFiber U x (smallEtaleTensorPresheaf.{u, w} X F G) ≫
      smallEtalePointTensorStalkMap.{u, w} X q F G =
      AddCommGrpCat.ofHom (TensorProduct.map
        (q.toPresheafFiber U x F).hom.toIntLinearMap
        (q.toPresheafFiber U x G).hom.toIntLinearMap).toAddMonoidHom :=
    q.toPresheafFiber_presheafFiberDesc _ _ U x
  have hv : TensorProduct.map
        (p.toPresheafFiber U (h.hom.app U x) F).hom.toIntLinearMap
        (p.toPresheafFiber U (h.hom.app U x) G).hom.toIntLinearMap =
      (TensorProduct.map (h.presheafFiber.app F).hom.toIntLinearMap
        (h.presheafFiber.app G).hom.toIntLinearMap).comp
        (TensorProduct.map (q.toPresheafFiber U x F).hom.toIntLinearMap
          (q.toPresheafFiber U x G).hom.toIntLinearMap) := by
    apply TensorProduct.ext'
    intro a b
    exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b)
      (ConcreteCategory.congr_hom (pointHom_presheafFiber_germ X h F U x) a).symm
      (ConcreteCategory.congr_hom (pointHom_presheafFiber_germ X h G U x) b).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun l => l ≫ smallEtalePointTensorStalkMap.{u, w} X p F G) ht).trans
      (hp.trans ((congrArg (fun l => AddCommGrpCat.ofHom l.toAddMonoidHom) hv).trans
        ((congrArg (fun l => l ≫ AddCommGrpCat.ofHom (TensorProduct.map
          (h.presheafFiber.app F).hom.toIntLinearMap
          (h.presheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom) hq).symm.trans
          (Category.assoc _ _ _)))))

set_option backward.isDefEq.respectTransparency.types false in
/-- Let X be a scheme in universe u, c = max(u, w), h : p → q a
morphism of points, and F, H abelian sheaves on its small étale site.
The tensor-sheaf stalk isomorphisms
τ_p : (F ⊗_sheaf H)_p ≅ F_p ⊗[ℤ] H_p satisfy
τ_p ∘ h*_(F⊗H) = (h*_F ⊗ h*_H) ∘ τ_q. -/
theorem smallEtalePointTensorSheafStalkIso_point_naturality (X : Scheme.{u})
    {p q : GrothendieckTopology.Point.{max u w} X.smallEtaleTopology} (h : p ⟶ q)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) :
    h.sheafFiber.app (smallEtaleTensorSheaf.{u, w} X F G) ≫
        (smallEtalePointTensorSheafStalkIso.{u, w} X p F G).hom =
      (smallEtalePointTensorSheafStalkIso.{u, w} X q F G).hom ≫
        AddCommGrpCat.ofHom (TensorProduct.map
          (h.sheafFiber.app F).hom.toIntLinearMap
          (h.sheafFiber.app G).hom.toIntLinearMap).toAddMonoidHom := by
  let T := smallEtaleTensorPresheaf.{u, w} X F.obj G.obj
  let ep := p.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}
  let eq := q.presheafToSheafCompSheafFiberIso AddCommGrpCat.{max u w}
  let ap := (p.presheafFiber (A := AddCommGrpCat.{max u w})).map (toSheafify X.smallEtaleTopology T)
  let aq := (q.presheafFiber (A := AddCommGrpCat.{max u w})).map (toSheafify X.smallEtaleTopology T)
  have hap : ap ≫ ep.hom.app T = 𝟙 _ := (ep.app T).inv_hom_id
  have haq : aq ≫ eq.hom.app T = 𝟙 _ := (eq.app T).inv_hom_id
  have hn : aq ≫ h.presheafFiber.app (sheafify X.smallEtaleTopology T) =
      h.presheafFiber.app T ≫ ap := h.presheafFiber.naturality (toSheafify X.smallEtaleTopology T)
  have ht := smallEtalePointTensorStalkMap_point_naturality.{u, w} X h F.obj G.obj
  apply (cancel_epi aq).1
  change aq ≫ (h.presheafFiber.app (sheafify X.smallEtaleTopology T) ≫
      (ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj)) =
    aq ≫ ((eq.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X q F.obj G.obj) ≫ _)
  calc
    _ = (aq ≫ h.presheafFiber.app (sheafify X.smallEtaleTopology T)) ≫
        ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj := by
      simp only [Category.assoc]
    _ = (h.presheafFiber.app T ≫ ap) ≫ ep.hom.app T ≫
        smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj :=
      congrArg (fun f => f ≫ ep.hom.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj) hn
    _ = h.presheafFiber.app T ≫ smallEtalePointTensorStalkMap.{u, w} X p F.obj G.obj := by
      rw [Category.assoc, ← Category.assoc ap, hap, Category.id_comp]
    _ = smallEtalePointTensorStalkMap.{u, w} X q F.obj G.obj ≫ _ := ht
    _ = _ := by
      rw [← Category.assoc aq, ← Category.assoc aq, haq, Category.id_comp]
      rfl

section Field

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
attribute [local instance] IsSepClosure.sep_closed

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For coefficient sheaves F, H and g ∈ G, the point tensor-stalk
isomorphism τ satisfies
τ ∘ g_(F⊗H) = (g_F ⊗ g_H) ∘ τ.
Thus the action on the tensor stalk is the diagonal Galois action. -/
theorem fieldPointTensorSheafStalkIso_galois
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (g : Gal(Ω/k)) :
    (fieldGaloisStalkMap.{u, w} k Ω g).app
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom =
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        ((fieldGaloisStalkMap.{u, w} k Ω g).app F).hom.toIntLinearMap
        ((fieldGaloisStalkMap.{u, w} k Ω g).app G).hom.toIntLinearMap).toAddMonoidHom :=
  smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldGaloisPointEndomorphism.{u, w} k Ω g) F G

local instance fieldNativeModuleDiscrete (M : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteTopology ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj M) := M.property

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For coefficient sheaves F, H, the stalk tensor comparison is an
isomorphism of discrete topological ℤ-representations
P(E(F ⊗_sheaf H)) ≅ P(E(F)) ⊗[ℤ] P(E(H)),
with the diagonal G-action and discrete tensor-coefficient topology. -/
def fieldPointTensorTopRepIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).obj
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) ≅
      ContinuousCohomology.discreteTensorCoefficient
        ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
          (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F))
        ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
          (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)) := by
  let A := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
  let B := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  let S := (ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)).obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G))
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  letI : TopologicalSpace T := T.hV3
  letI : IsTopologicalAddGroup T := T.hV4
  letI : ContinuousSMul ℤ T := T.hV5
  letI : DiscreteTopology T := ContinuousCohomology.discreteTensorCoefficient_discrete A B
  let e : S ≃+ T :=
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).addCommGroupIsoToAddEquiv
  have he (g : Gal(Ω/k)) (x : S) : e (S.ρ g x) = T.ρ g (e x) := by
    exact ConcreteCategory.congr_hom (fieldPointTensorSheafStalkIso_galois.{u, w} k Ω F G g) x
  let f : S ⟶ T := ConcreteCategory.ofHom (X := S) (Y := T)
    { toContinuousLinearMap := DiscreteAbelianAction.addHomContinuousLinearMap
        (TopModuleCat.of ℤ S) (TopModuleCat.of ℤ T) e.toAddMonoidHom
      isIntertwining' g := by
        apply ContinuousLinearMap.ext
        intro x
        exact he g x }
  let i : T ⟶ S := ConcreteCategory.ofHom (X := T) (Y := S)
    { toContinuousLinearMap := DiscreteAbelianAction.addHomContinuousLinearMap
        (TopModuleCat.of ℤ T) (TopModuleCat.of ℤ S) e.symm.toAddMonoidHom
      isIntertwining' g := by
        apply ContinuousLinearMap.ext
        intro x
        apply e.injective
        change e (e.symm (T.ρ g x)) = e (S.ρ g (e.symm x))
        rw [e.apply_symm_apply, he]
        exact congrArg (T.ρ g) (e.apply_symm_apply x).symm }
  exact
    { hom := f
      inv := i
      hom_inv_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply TopRep.hom_ext
        apply ContIntertwiningMap.ext
        apply ContinuousLinearMap.ext
        intro x
        exact e.apply_symm_apply x }

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
The underlying map of the topological tensor comparison on
E(F ⊗_sheaf H) is the canonical point tensor-stalk isomorphism
(F ⊗_sheaf H)_Ω → F_Ω ⊗[ℤ] H_Ω. -/
theorem fieldPointTensorTopRepIso_hom_apply
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : fieldGeometricStalkCarrier.{u, w} k Ω
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) :
    (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom x =
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom x := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For an étale k-scheme U, a geometric lift z ∈ U(Ω), and
a ∈ F(U), b ∈ H(U), the topological tensor-stalk comparison sends
the germ of the sheafified tensor section a ⊗ b at z to
germ_z(a) ⊗[ℤ] germ_z(b). -/
theorem fieldPointTensorTopRepIso_original_germ_tmul
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G).obj
        (smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b))) =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) F.obj a) ⊗ₜ[ℤ]
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) G.obj b) :=
  smallEtalePointTensorSheafStalkIso_section_tmul.{u, w} (Spec (.of k))
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G U (ULift.up z) a b

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For sheaf maps f : F → F′ and g : H → H′, the topological tensor
comparisons τ satisfy
τ_(F′,H′) ∘ P(E(f ⊗_sheaf g)) =
(P(E(f)) ⊗ P(E(g))) ∘ τ_(F,H).
The tensor maps use the discrete coefficient representations. -/
theorem fieldPointTensorTopRepIso_naturality
    {F F' G G' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : F ⟶ F') (g : G ⟶ G') :
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let J := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
    P.map (J.map (smallEtaleTensorSheafMap.{u, w} (Spec (.of k)) f g)) ≫
        (fieldPointTensorTopRepIso.{u, w} k Ω F' G').hom =
      (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom ≫
        ContinuousCohomology.discreteTensorCoefficientMap (P.map (J.map f)) (P.map (J.map g)) := by
  intro P J
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (smallEtalePointTensorSheafStalkIso_naturality.{u, w} (Spec (.of k))
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) f g) x

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For discrete continuous G-modules M, N, their tensor coefficient is
the abelian group M ⊗[ℤ] N with discrete topology and continuous
diagonal action g • (m ⊗ n) = (g • m) ⊗ (g • n). -/
def fieldTensorCoefficientModule (M N : FieldCohomologyModule.{u, w} k Ω) :
    FieldCohomologyModule.{u, w} k Ω := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let A := P.obj M
  let B := P.obj N
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  have hA : ((TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj A).IsContinuous := by
    change M.obj.obj.IsContinuous
    exact M.obj.property
  have hB : ((TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj B).IsContinuous := by
    change N.obj.obj.IsContinuous
    exact N.obj.property
  exact ⟨⟨(TopRep.toActionTopModFunc (k := ℤ) (G := Gal(Ω/k))).obj T,
    ContinuousCohomology.discreteTensorCoefficient_action_isContinuous A B hA hB⟩,
      ContinuousCohomology.discreteTensorCoefficient_discrete A B⟩

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
The underlying abelian group of the diagonal tensor coefficient
of M and N is the algebraic integer tensor product M ⊗[ℤ] N,
in coefficient universe c. -/
theorem fieldTensorCoefficientModule_carrier (M N : FieldCohomologyModule.{u, w} k Ω) :
    (DiscreteAbelianAction.underlying (fieldTensorCoefficientModule.{u, w} k Ω M N) : Type
        (max u w)) =
      TensorProduct ℤ (DiscreteAbelianAction.underlying M)
          (DiscreteAbelianAction.underlying N) := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For M, N discrete continuous G-modules, g ∈ G and m ∈ M, n ∈ N,
the tensor coefficient action has pure value
g • (m ⊗[ℤ] n) = (g • m) ⊗[ℤ] (g • n). -/
theorem fieldTensorCoefficientModule_action_tmul
    (M N : FieldCohomologyModule.{u, w} k Ω) (g : Gal(Ω/k)) :
    let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)
    let A := P.obj M
    let B := P.obj N
    letI : Module ℤ A := A.hV2
    letI : Module ℤ B := B.hV2
    ∀ (a : A) (b : B),
      ((fieldTensorCoefficientModule.{u, w} k Ω M N).obj.obj.ρ g).asHom.hom (a ⊗ₜ[ℤ] b) =
        A.ρ g a ⊗ₜ[ℤ] B.ρ g b := by
  intro P A B a b
  exact ContinuousCohomology.discreteTensorCoefficient_action_tmul A B g a b

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For coefficient sheaves F, H, the geometric tensor-stalk comparison
is an isomorphism E(F ⊗_sheaf H) ≅ E(F) ⊗[ℤ] E(H) in the
discrete continuous G-module category. -/
def fieldPointTensorGaloisIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≅
      fieldTensorCoefficientModule.{u, w} k Ω
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G) := by
  let P := ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let A := P.obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
  let B := P.obj ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  let T := ContinuousCohomology.discreteTensorCoefficient A B
  exact (DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))).preimageIso
    (fieldPointTensorTopRepIso.{u, w} k Ω F G ≪≫ (TopRep.toActionFromAction T).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
The underlying additive map of the Galois tensor-stalk isomorphism
equals the underlying map of its topological representation comparison.
Both give the canonical point tensor-stalk map. -/
theorem fieldPointTensorGaloisIso_hom_apply
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (x : fieldGeometricStalkCarrier.{u, w} k Ω
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)) :
    DiscreteAbelianAction.homToAdd (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom x =
      (fieldPointTensorTopRepIso.{u, w} k Ω F G).hom.hom x := by
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let e := fieldPointTensorTopRepIso.{u, w} k Ω F G
  let T := ContinuousCohomology.discreteTensorCoefficient
    ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F))
    ((ContinuousCohomology.discreteCoefficientTopRepFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).obj
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G))
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
    (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G)
  let N := fieldTensorCoefficientModule.{u, w} k Ω
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
  have h : P.map (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom =
      (e ≪≫ (TopRep.toActionFromAction T).symm).hom :=
    P.map_preimage (X := M) (Y := N) (e ≪≫ (TopRep.toActionFromAction T).symm).hom
  exact congrArg (fun f : P.obj M ⟶ P.obj N => f.hom x) h

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
If Φ is the equivariant-function inverse to E, the tensor sheaf
has the isomorphism F ⊗_sheaf H ≅ Φ(E(F) ⊗[ℤ] E(H)).
Its forward map is the equivalence unit followed by Φ of the
Galois tensor-stalk isomorphism. -/
def fieldTensorSheafInverseIso
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G ≅
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj
        (fieldTensorCoefficientModule.{u, w} k Ω
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
          ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)) :=
  (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.app
      (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≪≫
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).mapIso
      (fieldPointTensorGaloisIso.{u, w} k Ω F G)

set_option backward.isDefEq.respectTransparency.types false in
/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
For U ∈ Etale(Spec k), z ∈ U(Ω), a ∈ F(U), and b ∈ H(U),
the image of the tensor section a ⊗ b under
F ⊗_sheaf H ≅ Φ(E(F) ⊗[ℤ] E(H)) is the equivariant function
whose value at z is germ_z(a) ⊗[ℤ] germ_z(b). -/
theorem fieldTensorSheafInverseIso_original_germ_tmul
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    let V := fieldTensorCoefficientModule.{u, w} k Ω
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj F)
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj G)
    let h : FieldEquivariantFunctions.{u, w} k Ω U V :=
      (fieldTensorSheafInverseIso.{u, w} k Ω F G).hom.hom.app (op U)
        (smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b))
    h z =
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) F.obj a) ⊗ₜ[ℤ]
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) G.obj b) := by
  intro V h
  let T := smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G
  let M := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj T
  let η : T ⟶ (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M :=
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app T
  let d : M ⟶ V := (fieldPointTensorGaloisIso.{u, w} k Ω F G).hom
  let c := smallEtaleTensorSheafSectionMap.{u, w} (Spec (.of k)) F G (op U) (a ⊗ₜ[ℤ] b)
  let h₀ : FieldEquivariantFunctions.{u, w} k Ω U M := η.hom.app (op U) c
  have hm := fieldSheafGaloisEquivalence_inverse_map.{u, w} k Ω d U h₀ z
  have hu : h₀ z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) T.obj c :=
    fieldSheafGaloisEquivalence_unit_germ.{u, w} k Ω T U z c
  exact hm.trans ((congrArg (DiscreteAbelianAction.homToAdd d) hu).trans
    ((fieldPointTensorGaloisIso_hom_apply.{u, w} k Ω F G _).trans
      (fieldPointTensorTopRepIso_original_germ_tmul.{u, w} k Ω F G U z a b)))

variable (Ψ : Type u) [Field Ψ] [Algebra k Ψ] [IsSepClosed Ψ]

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Ψ be any separably closed k-field in universe u and
σ : Ω →ₐ[k] Ψ. For the closure-change stalk comparisons χ,
the tensor square is
τ_Ψ ∘ χ_(F⊗H) = (χ_F ⊗ χ_H) ∘ τ_Ω
for every pair of coefficient sheaves F, H. -/
theorem fieldClosureCommonStalkIso_tensor
    (σ : Ω →ₐ[k] Ψ)
    (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app
        (smallEtaleTensorSheaf.{u, w} (Spec (.of k)) F G) ≫
      (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ψ)) F G).hom =
    (smallEtalePointTensorSheafStalkIso.{u, w} (Spec (.of k))
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)) F G).hom ≫
      AddCommGrpCat.ofHom (TensorProduct.map
        ((fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app F).hom.toIntLinearMap
        ((fieldClosureCommonStalkIso.{u, w} k Ω Ψ σ).hom.app
            G).hom.toIntLinearMap).toAddMonoidHom :=
  smallEtalePointTensorSheafStalkIso_point_naturality.{u, w} (Spec (.of k))
    (fieldClosureCommonPointIso.{u, w} k Ω Ψ σ).hom F G

end Field

end AlgebraicGeometry.Scheme.DerivedSections

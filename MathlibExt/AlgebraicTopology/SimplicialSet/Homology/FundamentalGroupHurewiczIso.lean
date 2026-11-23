/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.Homology.FundamentalGroupHomologyComparison
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Simplicial H1 and the abelianized fundamental group

For a connected simplicial set with a chosen base vertex, this file
constructs the inverse to the degree-one Hurewicz map by closing every edge
with chosen fundamental-groupoid connectors.  The triangle relation kills
two-boundaries after abelianization, and the two concrete round trips give
the canonical H1/abelianized-fundamental-group isomorphism.

This is a combinatorial simplicial theorem.  It makes no generic topological
Hurewicz, connector naturality, finite-BGL, kernel, plus-construction, or
`Q = +` claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/-- In a connected simplicial set, the fundamental-groupoid objects
represented by any two vertices are isomorphic. -/
theorem nonempty_fundamentalGroupoid_iso_of_isConnected
    (X : SSet.{u}) [X.IsConnected] (x y : X _⦋0⦌) :
    Nonempty
      (SSet.FundamentalGroupoid.mk x ≅
        SSet.FundamentalGroupoid.mk y) := by
  have h : SSet.π₀.mk x = SSet.π₀.mk y := Subsingleton.elim _ _
  rw [SSet.π₀.mk_eq_mk_iff] at h
  induction h with
  | rel x y h =>
      obtain ⟨e⟩ := h
      exact ⟨asIso (SSet.FundamentalGroupoid.homMk e)⟩
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih => exact ⟨ih.some.symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some.trans ih₂.some⟩

/-- A chosen connector in the simplicial fundamental groupoid from the base
vertex to another vertex. -/
noncomputable def fundamentalGroupoidConnector
    (X : SSet.{u}) [X.IsConnected] (x y : X _⦋0⦌) :
    SSet.FundamentalGroupoid.mk x ≅
      SSet.FundamentalGroupoid.mk y :=
  (nonempty_fundamentalGroupoid_iso_of_isConnected X x y).some

/-- Close an edge to a based loop using the chosen connectors to its source
and target. -/
noncomputable def basedEdgeLoop
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : X _⦋0⦌} (e : X.Edge a b) :
    End (SSet.FundamentalGroupoid.mk x) :=
  End.of ((fundamentalGroupoidConnector X x a).hom ≫
    SSet.FundamentalGroupoid.homMk e ≫
      (fundamentalGroupoidConnector X x b).inv)

/-- The class in the additive abelianization represented by a closed edge. -/
noncomputable def basedEdgeAbelianizationClass
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : X _⦋0⦌} (e : X.Edge a b) :
    Additive
      (Abelianization (End (SSet.FundamentalGroupoid.mk x))) :=
  Additive.ofMul (Abelianization.of (basedEdgeLoop X x e))

/-- Transporting the endpoints of an edge does not change its chosen-closed
class after the same endpoint equalities are eliminated. -/
theorem basedEdgeAbelianizationClass_ofEq
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b a' b' : X _⦋0⦌} (e : X.Edge a b)
    (ha : a = a') (hb : b = b') :
    basedEdgeAbelianizationClass X x (e.ofEq ha hb) =
      basedEdgeAbelianizationClass X x e := by
  subst a'
  subst b'
  rfl

/-- Replacing an edge by the canonical edge structure on the same
one-simplex does not change its closed class. -/
theorem basedEdgeAbelianizationClass_mk'_edge
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : X _⦋0⦌} (e : X.Edge a b) :
    basedEdgeAbelianizationClass X x (SSet.Edge.mk' e.edge) =
      basedEdgeAbelianizationClass X x e := by
  calc
    basedEdgeAbelianizationClass X x (SSet.Edge.mk' e.edge) =
        basedEdgeAbelianizationClass X x
          ((SSet.Edge.mk' e.edge).ofEq e.src_eq e.tgt_eq) :=
      (basedEdgeAbelianizationClass_ofEq X x
        (SSet.Edge.mk' e.edge) e.src_eq e.tgt_eq).symm
    _ = basedEdgeAbelianizationClass X x e := by
      congr 1

/-- The coefficient homomorphism which sends the integral generator to the
abelianization class of a closed edge. -/
noncomputable def simplexAbelianizationCoefficientHom
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (s : X _⦋1⦌) :
    ULift.{u} ℤ →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) :=
  uliftZMultiplesHom _
    (basedEdgeAbelianizationClass X x (SSet.Edge.mk' s))

/-- Extend the closed-edge class additively from one-simplex generators to
all integral one-chains. -/
noncomputable def oneChainsToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralOneChains X →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) :=
  ((X.isColimitChainComplexXCofan
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u}) 1).desc
    (Cofan.mk
      (AddCommGrpCat.of
        (Additive
          (Abelianization (End (SSet.FundamentalGroupoid.mk x)))))
      (fun s ↦ AddCommGrpCat.ofHom
        (simplexAbelianizationCoefficientHom X x s)))).hom

/-- Formula for the one-chain map on a simplex generator. -/
theorem oneChainsToAbelianization_simplex
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (s : X _⦋1⦌) :
    oneChainsToAbelianization X x (simplexOneChain X s) =
      basedEdgeAbelianizationClass X x (SSet.Edge.mk' s) := by
  let Z : AddCommGrpCat.{u} :=
    AlgebraicTopology.singularIntegralCoefficients
  let A : AddCommGrpCat.{u} :=
    AddCommGrpCat.of
      (Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))))
  let c : Cofan (fun (_ : X _⦋1⦌) ↦ Z) :=
    Cofan.mk A (fun t ↦ AddCommGrpCat.ofHom
      (simplexAbelianizationCoefficientHom X x t))
  have hfac := (X.isColimitChainComplexXCofan Z 1).fac c ⟨s⟩
  have happ := ConcreteCategory.congr_hom hfac (ULift.up (1 : ℤ))
  change oneChainsToAbelianization X x (simplexOneChain X s) =
    simplexAbelianizationCoefficientHom X x s (ULift.up (1 : ℤ)) at happ
  have hup : AddEquiv.ulift (ULift.up (1 : ℤ)) = 1 := rfl
  rw [simplexAbelianizationCoefficientHom,
    uliftZMultiplesHom_apply_apply, hup, one_zsmul] at happ
  exact happ

/-- Closing the three edges of a two-simplex with the chosen connectors
gives the signed triangle relation after abelianization. -/
theorem basedEdgeAbelianizationClass_comp
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    basedEdgeAbelianizationClass X x e₁₂ -
        basedEdgeAbelianizationClass X x e₀₂ +
      basedEdgeAbelianizationClass X x e₀₁ = 0 := by
  have hloop :
      basedEdgeLoop X x e₁₂ * basedEdgeLoop X x e₀₁ =
        basedEdgeLoop X x e₀₂ := by
    apply End.ext
    simp only [End.mul_asHom, basedEdgeLoop, Category.assoc, Iso.inv_hom_id_assoc,
      h.homMk_comp_assoc]
  have hab :
      basedEdgeAbelianizationClass X x e₁₂ +
          basedEdgeAbelianizationClass X x e₀₁ =
        basedEdgeAbelianizationClass X x e₀₂ := by
    apply Additive.toMul.injective
    change Abelianization.of (basedEdgeLoop X x e₁₂) *
        Abelianization.of (basedEdgeLoop X x e₀₁) =
      Abelianization.of (basedEdgeLoop X x e₀₂)
    rw [← map_mul]
    exact congrArg Abelianization.of hloop
  rw [← hab]
  abel

/-- The closed-edge map vanishes on integral two-boundaries. -/
theorem oneChainsToAbelianization_comp_d
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    (oneChainsToAbelianization X x).comp
        ((X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).d 2 1).hom = 0 := by
  let Z : AddCommGrpCat.{u} :=
    AlgebraicTopology.singularIntegralCoefficients
  let A : AddCommGrpCat.{u} :=
    AddCommGrpCat.of
      (Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))))
  let K := X.chainComplex Z
  have hcat : K.d 2 1 ≫
      AddCommGrpCat.ofHom (oneChainsToAbelianization X x) = 0 := by
    apply X.chainComplex_hom_ext
    intro s
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv A).injective
    change oneChainsToAbelianization X x
        ((X.ιChainComplex s ≫ K.d 2 1) (ULift.up (1 : ℤ))) = 0
    rw [X.ιChainComplex_d]
    change oneChainsToAbelianization X x
      ((∑ i : Fin 3, ((-1 : ℤ) ^ i.val) •
        (X.ιChainComplex
          (R := AlgebraicTopology.singularIntegralCoefficients)
          (X.δ i s)).hom (ULift.up (1 : ℤ)))) = 0
    rw [Fin.sum_univ_three]
    norm_num [simplexOneChain]
    have h₀ := oneChainsToAbelianization_simplex X x (X.δ 0 s)
    have h₁ := oneChainsToAbelianization_simplex X x (X.δ 1 s)
    have h₂ := oneChainsToAbelianization_simplex X x (X.δ 2 s)
    change oneChainsToAbelianization X x
        ((AddCommGrpCat.Hom.hom
          (X.ιChainComplex
            (R := AlgebraicTopology.singularIntegralCoefficients)
            (X.δ 0 s))) (ULift.up (1 : ℤ))) = _ at h₀
    change oneChainsToAbelianization X x
        ((AddCommGrpCat.Hom.hom
          (X.ιChainComplex
            (R := AlgebraicTopology.singularIntegralCoefficients)
            (X.δ 1 s))) (ULift.up (1 : ℤ))) = _ at h₁
    change oneChainsToAbelianization X x
        ((AddCommGrpCat.Hom.hom
          (X.ιChainComplex
            (R := AlgebraicTopology.singularIntegralCoefficients)
            (X.δ 2 s))) (ULift.up (1 : ℤ))) = _ at h₂
    rw [h₀, h₁, h₂]
    let e₀₁ := SSet.Edge.mk' (X.δ 2 s)
    let e₁₂' := SSet.Edge.mk' (X.δ 0 s)
    let e₀₂' := SSet.Edge.mk' (X.δ 1 s)
    have h₁₂src : X.δ 1 (X.δ 0 s) = X.δ 0 (X.δ 2 s) := by
      simpa using (X.δ_comp_δ_apply
        (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide) s).symm
    have h₀₂src : X.δ 1 (X.δ 1 s) = X.δ 1 (X.δ 2 s) := by
      simpa using X.δ_comp_δ_self_apply (i := (1 : Fin 2)) s
    have h₀₂tgt : X.δ 0 (X.δ 1 s) = X.δ 0 (X.δ 0 s) := by
      simpa using (X.δ_comp_δ_self_apply (i := (0 : Fin 2)) s).symm
    let e₁₂ : X.Edge (X.δ 0 (X.δ 2 s)) (X.δ 0 (X.δ 0 s)) :=
      e₁₂'.ofEq h₁₂src rfl
    let e₀₂ : X.Edge (X.δ 1 (X.δ 2 s)) (X.δ 0 (X.δ 0 s)) :=
      e₀₂'.ofEq h₀₂src h₀₂tgt
    let h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂ :=
      SSet.Edge.CompStruct.mk s rfl rfl rfl
    have htriangle := basedEdgeAbelianizationClass_comp X x h
    rw [basedEdgeAbelianizationClass_ofEq,
      basedEdgeAbelianizationClass_ofEq] at htriangle
    simpa only [sub_eq_add_neg] using htriangle
  exact congrArg AddCommGrpCat.Hom.hom hcat

/-- The closed-edge map descends from one-chains to one-chains modulo
two-boundaries. -/
noncomputable def oneChainQuotientToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    oneChainQuotient X →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) := by
  refine QuotientAddGroup.lift (oneChainBoundaries X)
    (oneChainsToAbelianization X x) ?_
  rintro z ⟨a, rfl⟩
  rw [AddMonoidHom.mem_ker]
  have h := congrArg (fun f ↦ f a)
    (oneChainsToAbelianization_comp_d X x)
  exact h

@[simp]
theorem oneChainQuotientToAbelianization_mk
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (c : integralOneChains X) :
    oneChainQuotientToAbelianization X x
        (QuotientAddGroup.mk' _ c) =
      oneChainsToAbelianization X x c :=
  rfl

/-- Restrict the quotient one-chain map to classes with zero boundary. -/
noncomputable def oneChainBoundaryKerToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    AddMonoidHom.ker (oneChainBoundary X) →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) where
  toFun z := oneChainQuotientToAbelianization X x z.val
  map_zero' := by simp
  map_add' _ _ := by simp

/-- Restrict the closed-edge map to integral one-cycles. -/
noncomputable def oneCyclesToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralOneCycles X →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) where
  toFun z := oneChainsToAbelianization X x z.val
  map_zero' := by simp
  map_add' _ _ := by simp

/-- Concrete two-boundaries lie in the kernel of the closed-edge map on
cycles. -/
theorem oneBoundaries_le_ker_oneCyclesToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    AddMonoidHom.range (oneBoundariesToCycles X) ≤
      AddMonoidHom.ker (oneCyclesToAbelianization X x) := by
  rintro z ⟨a, rfl⟩
  rw [AddMonoidHom.mem_ker]
  change oneChainsToAbelianization X x
    (((X.chainComplex
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u})).d 2 1).hom a) = 0
  have h := congrArg (fun f ↦ f a)
    (oneChainsToAbelianization_comp_d X x)
  exact h

/-- The connector-closed edge construction descends to the concrete
cycles-modulo-boundaries model of integral degree-one homology. -/
noncomputable def homologyOneQuotientToAbelianization
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralHomologyOneQuotient X →+
      Additive
        (Abelianization (End (SSet.FundamentalGroupoid.mk x))) :=
  QuotientAddGroup.lift _ (oneCyclesToAbelianization X x)
    (oneBoundaries_le_ker_oneCyclesToAbelianization X x)

@[simp]
theorem homologyOneQuotientToAbelianization_mk
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (z : integralOneCycles X) :
    homologyOneQuotientToAbelianization X x
        (QuotientAddGroup.mk' _ z) =
      oneChainsToAbelianization X x z.val :=
  rfl

/-- The direct cycles descent agrees with passage through the kernel of the
descended one-chain boundary. -/
theorem homologyOneQuotientToAbelianization_eq
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    homologyOneQuotientToAbelianization X x =
      (oneChainBoundaryKerToAbelianization X x).comp
        (homologyOneQuotientAddEquivOneChainBoundaryKer X).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ z => rfl

/-- Close an arbitrary fundamental-groupoid morphism with the chosen
connectors. -/
noncomputable def basedMorphismLoop
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : SSet.FundamentalGroupoid X} (q : a ⟶ b) :
    End (SSet.FundamentalGroupoid.mk x) :=
  End.of ((fundamentalGroupoidConnector X x a.pt).hom ≫ q ≫
    (fundamentalGroupoidConnector X x b.pt).inv)

/-- The abelianization class of an arbitrary connector-closed
fundamental-groupoid morphism. -/
noncomputable def basedMorphismAbelianizationClass
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : SSet.FundamentalGroupoid X} (q : a ⟶ b) :
    Additive
      (Abelianization (End (SSet.FundamentalGroupoid.mk x))) :=
  Additive.ofMul (Abelianization.of (basedMorphismLoop X x q))

@[simp]
theorem basedMorphismAbelianizationClass_homMk
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : X _⦋0⦌} (e : X.Edge a b) :
    basedMorphismAbelianizationClass X x
        (SSet.FundamentalGroupoid.homMk e) =
      basedEdgeAbelianizationClass X x e :=
  rfl

@[simp]
theorem basedMorphismAbelianizationClass_inv
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : SSet.FundamentalGroupoid X} (q : a ⟶ b) :
    basedMorphismAbelianizationClass X x (inv q) =
      -basedMorphismAbelianizationClass X x q := by
  apply Additive.toMul.injective
  change Abelianization.of (basedMorphismLoop X x (inv q)) =
    (Abelianization.of (basedMorphismLoop X x q))⁻¹
  rw [← map_inv]
  congr 1
  apply End.ext
  apply (cancel_mono (basedMorphismLoop X x q).asHom).1
  change (basedMorphismLoop X x (inv q)).asHom ≫
      (basedMorphismLoop X x q).asHom =
    Groupoid.inv ((basedMorphismLoop X x q).asHom) ≫
      (basedMorphismLoop X x q).asHom
  rw [Groupoid.inv_comp]
  simp only [basedMorphismLoop, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Groupoid.inv_eq_inv q,
    ← Category.assoc (Groupoid.inv q) q,
    Groupoid.inv_comp, Category.id_comp, Iso.hom_inv_id]

@[simp]
theorem basedMorphismAbelianizationClass_comp
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b c : SSet.FundamentalGroupoid X}
    (q : a ⟶ b) (r : b ⟶ c) :
    basedMorphismAbelianizationClass X x q +
        basedMorphismAbelianizationClass X x r =
      basedMorphismAbelianizationClass X x (q ≫ r) := by
  have hloop :
      basedMorphismLoop X x r * basedMorphismLoop X x q =
        basedMorphismLoop X x (q ≫ r) := by
    apply End.ext
    simp only [End.mul_asHom, basedMorphismLoop, Category.assoc,
      Iso.inv_hom_id_assoc]
  apply Additive.toMul.injective
  change Abelianization.of (basedMorphismLoop X x q) *
      Abelianization.of (basedMorphismLoop X x r) =
    Abelianization.of (basedMorphismLoop X x (q ≫ r))
  rw [mul_comm, ← map_mul]
  exact congrArg Abelianization.of hloop

/-- At the base vertex, connector closing only conjugates a loop and hence
does not change its abelianization class. -/
theorem basedMorphismAbelianizationClass_end
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    basedMorphismAbelianizationClass X x q.asHom =
      Additive.ofMul (Abelianization.of q) := by
  let p := fundamentalGroupoidConnector X x x
  let pinv : End (SSet.FundamentalGroupoid.mk x) := End.of p.inv
  let phom : End (SSet.FundamentalGroupoid.mk x) := End.of p.hom
  have hpinv : pinv * phom = 1 := by
    apply End.ext
    change p.hom ≫ p.inv = 𝟙 _
    exact p.hom_inv_id
  have hp : Abelianization.of pinv * Abelianization.of phom = 1 := by
    rw [← map_mul]
    rw [hpinv]
    exact map_one Abelianization.of
  apply Additive.toMul.injective
  change Abelianization.of (basedMorphismLoop X x q.asHom) =
    Abelianization.of q
  have hloop : basedMorphismLoop X x q.asHom = pinv * q * phom := rfl
  rw [hloop]
  rw [map_mul, map_mul]
  calc
    Abelianization.of pinv * Abelianization.of q *
          Abelianization.of phom =
        Abelianization.of q *
          (Abelianization.of pinv * Abelianization.of phom) := by
      ac_rfl
    _ = Abelianization.of q := by rw [hp, mul_one]

/-- In the quotient one-chain groupoid, inversion negates the underlying
quotient chain. -/
theorem oneChainGroupoid_inv_val
    (X : SSet.{u}) {a b : OneChainGroupoid X} (q : a ⟶ b) :
    (Groupoid.inv q).val = -q.val :=
  rfl

/-- Evaluating the descended closed-edge map on the quotient chain carried
by a fundamental-groupoid morphism gives its connector-closed class. -/
theorem oneChainQuotientToAbelianization_map
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : SSet.FundamentalGroupoid X} (q : a ⟶ b) :
    oneChainQuotientToAbelianization X x
        ((fundamentalGroupoidToOneChainGroupoid X).map q).val =
      basedMorphismAbelianizationClass X x q := by
  induction q using SSet.FundamentalGroupoid.hom_rec with
  | homMk e =>
      rw [fundamentalGroupoidToOneChainGroupoid_map_homMk]
      change oneChainQuotientToAbelianization X x
          (edgeOneChainClass e) = _
      rw [edgeOneChainClass, oneChainQuotientToAbelianization_mk,
        oneChainsToAbelianization_simplex]
      exact basedEdgeAbelianizationClass_mk'_edge X x e
  | inv q hq =>
      rw [Functor.map_inv]
      rw [← Groupoid.inv_eq_inv, oneChainGroupoid_inv_val]
      rw [map_neg, hq, basedMorphismAbelianizationClass_inv]
  | comp q r hq hr =>
      rw [Functor.map_comp]
      change oneChainQuotientToAbelianization X x
          (((fundamentalGroupoidToOneChainGroupoid X).map q).val +
            ((fundamentalGroupoidToOneChainGroupoid X).map r).val) = _
      rw [map_add, hq, hr, basedMorphismAbelianizationClass_comp]

/-- The concrete forward Hurewicz map, written additively. -/
noncomputable def fundamentalGroupAbelianizationConcreteHomologyOneAddHom
    (X : SSet.{u}) (x : X _⦋0⦌) :
    Additive (Abelianization (End (SSet.FundamentalGroupoid.mk x))) →+
      integralHomologyOneQuotient X :=
  (fundamentalGroupAbelianizationConcreteHomologyOneHom X x).toAdditive

/-- The connector-closed inverse is a left inverse to the concrete forward
map on classes represented by based loops. -/
theorem homologyOneQuotientToAbelianization_forward_of
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (q : End (SSet.FundamentalGroupoid.mk x)) :
    homologyOneQuotientToAbelianization X x
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x
          (Additive.ofMul (Abelianization.of q))) =
      Additive.ofMul (Abelianization.of q) := by
  rw [homologyOneQuotientToAbelianization_eq]
  change oneChainBoundaryKerToAbelianization X x
      ((homologyOneQuotientAddEquivOneChainBoundaryKer X)
        (Multiplicative.toAdd
          (fundamentalGroupConcreteHomologyOneHom X x q))) = _
  have he := (homologyOneQuotientAddEquivOneChainBoundaryKer X).apply_symm_apply
    (Multiplicative.toAdd
      (oneChainGroupoidEndMulEquivBoundaryKer X x
        ((fundamentalGroupoidToOneChainGroupoid X).mapEnd
          (SSet.FundamentalGroupoid.mk x) q)))
  change (homologyOneQuotientAddEquivOneChainBoundaryKer X)
      (Multiplicative.toAdd
        (fundamentalGroupConcreteHomologyOneHom X x q)) = _ at he
  rw [he]
  change oneChainQuotientToAbelianization X x
      ((fundamentalGroupoidToOneChainGroupoid X).map q.asHom).val = _
  rw [oneChainQuotientToAbelianization_map,
    basedMorphismAbelianizationClass_end]

/-- The concrete connector-closed inverse is a left inverse to the forward
map on the entire abelianization. -/
theorem homologyOneQuotientToAbelianization_comp_forward
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    (homologyOneQuotientToAbelianization X x).comp
        (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x) =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  rintro ⟨z⟩
  exact homologyOneQuotientToAbelianization_forward_of X x z

/-- The quotient one-chain carried by the chosen connector from the base
vertex to `y`. -/
noncomputable def connectorOneChainClass
    (X : SSet.{u}) [X.IsConnected] (x y : X _⦋0⦌) :
    oneChainQuotient X :=
  ((fundamentalGroupoidToOneChainGroupoid X).map
    (fundamentalGroupoidConnector X x y).hom).val

/-- The coefficient homomorphism selecting the quotient chain carried by a
chosen connector. -/
noncomputable def vertexConnectorCoefficientHom
    (X : SSet.{u}) [X.IsConnected] (x y : X _⦋0⦌) :
    ULift.{u} ℤ →+ oneChainQuotient X :=
  uliftZMultiplesHom _ (connectorOneChainClass X x y)

/-- Extend chosen connector chains additively over integral zero-chains. -/
noncomputable def zeroChainsToConnectorOneChain
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralZeroChains X →+ oneChainQuotient X :=
  ((X.isColimitChainComplexXCofan
      (AlgebraicTopology.singularIntegralCoefficients :
        AddCommGrpCat.{u}) 0).desc
    (Cofan.mk (AddCommGrpCat.of (oneChainQuotient X))
      (fun y ↦ AddCommGrpCat.ofHom
        (vertexConnectorCoefficientHom X x y)))).hom

/-- Formula for the connector-chain map on a vertex generator. -/
theorem zeroChainsToConnectorOneChain_vertex
    (X : SSet.{u}) [X.IsConnected] (x y : X _⦋0⦌) :
    zeroChainsToConnectorOneChain X x (vertexChain X y) =
      connectorOneChainClass X x y := by
  let Z : AddCommGrpCat.{u} :=
    AlgebraicTopology.singularIntegralCoefficients
  let Q : AddCommGrpCat.{u} := AddCommGrpCat.of (oneChainQuotient X)
  let c : Cofan (fun (_ : X _⦋0⦌) ↦ Z) :=
    Cofan.mk Q (fun z ↦ AddCommGrpCat.ofHom
      (vertexConnectorCoefficientHom X x z))
  have hfac := (X.isColimitChainComplexXCofan Z 0).fac c ⟨y⟩
  have happ := ConcreteCategory.congr_hom hfac (ULift.up (1 : ℤ))
  change zeroChainsToConnectorOneChain X x (vertexChain X y) =
    vertexConnectorCoefficientHom X x y (ULift.up (1 : ℤ)) at happ
  have hup : AddEquiv.ulift (ULift.up (1 : ℤ)) = 1 := rfl
  rw [vertexConnectorCoefficientHom,
    uliftZMultiplesHom_apply_apply, hup, one_zsmul] at happ
  exact happ

/-- Composition in the quotient one-chain groupoid adds the underlying
quotient chains. -/
theorem oneChainGroupoid_comp_val
    (X : SSet.{u}) {a b c : OneChainGroupoid X}
    (q : a ⟶ b) (r : b ⟶ c) :
    (q ≫ r).val = q.val + r.val :=
  rfl

/-- The quotient chain carried by a connector-closed edge is the edge
generator plus the source connector and minus the target connector. -/
theorem fundamentalGroupoidToOneChainGroupoid_map_basedEdgeLoop_val
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    {a b : X _⦋0⦌} (e : X.Edge a b) :
    (((fundamentalGroupoidToOneChainGroupoid X).mapEnd
        (SSet.FundamentalGroupoid.mk x)
        (basedEdgeLoop X x e)).asHom).val =
      connectorOneChainClass X x a + edgeOneChainClass e -
        connectorOneChainClass X x b := by
  change ((fundamentalGroupoidToOneChainGroupoid X).map
      (basedEdgeLoop X x e).asHom).val = _
  rw [basedEdgeLoop, ← Category.assoc, Functor.map_comp, Functor.map_comp,
    fundamentalGroupoidToOneChainGroupoid_map_homMk,
    oneChainGroupoid_comp_val]
  change (((fundamentalGroupoidToOneChainGroupoid X).map
      (fundamentalGroupoidConnector X x a).hom).val +
        edgeOneChainClass e) +
      ((fundamentalGroupoidToOneChainGroupoid X).map
        (fundamentalGroupoidConnector X x b).inv).val = _
  have hinv :
      (fundamentalGroupoidToOneChainGroupoid X).map
          (fundamentalGroupoidConnector X x b).inv =
        inv ((fundamentalGroupoidToOneChainGroupoid X).map
          (fundamentalGroupoidConnector X x b).hom) :=
    IsIso.eq_inv_of_hom_inv_id
      ((fundamentalGroupoidToOneChainGroupoid X).map_hom_inv'
        (fundamentalGroupoidConnector X x b))
  rw [hinv, ← Groupoid.inv_eq_inv,
    oneChainGroupoid_inv_val]
  simp only [connectorOneChainClass, sub_eq_add_neg]

/-- Apply the inverse on one-chains, then the concrete forward map, and
forget the zero-boundary witness. -/
noncomputable def oneChainsHurewiczRoundTrip
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralOneChains X →+ oneChainQuotient X :=
  (AddMonoidHom.ker (oneChainBoundary X)).subtype.comp
    ((homologyOneQuotientAddEquivOneChainBoundaryKer X).toAddMonoidHom.comp
      ((fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x).comp
        (oneChainsToAbelianization X x)))

/-- Generator formula for the one-chain Hurewicz round trip. -/
theorem oneChainsHurewiczRoundTrip_simplex
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (s : X _⦋1⦌) :
    oneChainsHurewiczRoundTrip X x (simplexOneChain X s) =
      connectorOneChainClass X x (X.δ 1 s) +
        edgeOneChainClass (SSet.Edge.mk' s) -
          connectorOneChainClass X x (X.δ 0 s) := by
  change ((homologyOneQuotientAddEquivOneChainBoundaryKer X)
      (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x
        (oneChainsToAbelianization X x (simplexOneChain X s)))).val = _
  rw [oneChainsToAbelianization_simplex]
  change ((homologyOneQuotientAddEquivOneChainBoundaryKer X)
      (Multiplicative.toAdd
        (fundamentalGroupConcreteHomologyOneHom X x
          (basedEdgeLoop X x (SSet.Edge.mk' s))))).val = _
  have he := (homologyOneQuotientAddEquivOneChainBoundaryKer X).apply_symm_apply
    (Multiplicative.toAdd
      (oneChainGroupoidEndMulEquivBoundaryKer X x
        ((fundamentalGroupoidToOneChainGroupoid X).mapEnd
          (SSet.FundamentalGroupoid.mk x)
          (basedEdgeLoop X x (SSet.Edge.mk' s)))))
  change (homologyOneQuotientAddEquivOneChainBoundaryKer X)
      (Multiplicative.toAdd
        (fundamentalGroupConcreteHomologyOneHom X x
          (basedEdgeLoop X x (SSet.Edge.mk' s)))) = _ at he
  rw [he]
  exact fundamentalGroupoidToOneChainGroupoid_map_basedEdgeLoop_val
    X x (SSet.Edge.mk' s)

/-- The identity on quotient one-chains, corrected by the chosen connector
chain applied to the one-chain boundary. -/
noncomputable def oneChainsConnectorCorrection
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    integralOneChains X →+ oneChainQuotient X :=
  QuotientAddGroup.mk' (oneChainBoundaries X) -
    (zeroChainsToConnectorOneChain X x).comp
      ((X.chainComplex
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u})).d 1 0).hom

/-- On every one-chain, the Hurewicz round trip differs from its quotient
class by the connector chain of its boundary. -/
theorem oneChainsHurewiczRoundTrip_eq_connectorCorrection
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    oneChainsHurewiczRoundTrip X x =
      oneChainsConnectorCorrection X x := by
  let Z : AddCommGrpCat.{u} :=
    AlgebraicTopology.singularIntegralCoefficients
  let Q : AddCommGrpCat.{u} := AddCommGrpCat.of (oneChainQuotient X)
  let K := X.chainComplex Z
  have hcat : AddCommGrpCat.ofHom (oneChainsHurewiczRoundTrip X x) =
      AddCommGrpCat.ofHom (oneChainsConnectorCorrection X x) := by
    apply X.chainComplex_hom_ext
    intro s
    apply (AddCommGrpCat.uliftZMultiplesAddEquiv Q).injective
    change oneChainsHurewiczRoundTrip X x (simplexOneChain X s) =
      oneChainsConnectorCorrection X x (simplexOneChain X s)
    rw [oneChainsHurewiczRoundTrip_simplex]
    have hd : K.d 1 0 (simplexOneChain X s) =
        vertexChain X (X.δ 0 s) - vertexChain X (X.δ 1 s) := by
      simpa only [edgeOneChainClass, SSet.Edge.mk'_edge,
        oneChainBoundary_mk] using
          oneChainBoundary_edgeOneChainClass (SSet.Edge.mk' s)
    rw [oneChainsConnectorCorrection, AddMonoidHom.sub_apply,
      AddMonoidHom.comp_apply, hd, map_sub,
      zeroChainsToConnectorOneChain_vertex,
      zeroChainsToConnectorOneChain_vertex]
    change connectorOneChainClass X x (X.δ 1 s) +
          edgeOneChainClass (SSet.Edge.mk' s) -
        connectorOneChainClass X x (X.δ 0 s) =
      edgeOneChainClass (SSet.Edge.mk' s) -
        (connectorOneChainClass X x (X.δ 0 s) -
          connectorOneChainClass X x (X.δ 1 s))
    abel
  exact congrArg AddCommGrpCat.Hom.hom hcat

/-- The concrete forward map is a left inverse to connector closing on a
class represented by an integral one-cycle. -/
theorem fundamentalGroupAbelianizationConcreteHomologyOneAddHom_inverse_mk
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌)
    (z : integralOneCycles X) :
    fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x
        (homologyOneQuotientToAbelianization X x
          (QuotientAddGroup.mk' _ z)) =
      QuotientAddGroup.mk' _ z := by
  rw [homologyOneQuotientToAbelianization_mk]
  apply (homologyOneQuotientAddEquivOneChainBoundaryKer X).injective
  apply Subtype.ext
  change oneChainsHurewiczRoundTrip X x z.val =
    (z.val : oneChainQuotient X)
  rw [oneChainsHurewiczRoundTrip_eq_connectorCorrection]
  change (z.val : oneChainQuotient X) -
      zeroChainsToConnectorOneChain X x
        (((X.chainComplex
          (AlgebraicTopology.singularIntegralCoefficients :
            AddCommGrpCat.{u})).d 1 0).hom z.val) =
    (z.val : oneChainQuotient X)
  rw [z.prop, map_zero, sub_zero]

/-- The concrete forward Hurewicz map and connector-closed inverse are
mutual inverses. -/
theorem fundamentalGroupAbelianizationConcreteHomologyOneAddHom_comp_inverse
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    (fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x).comp
        (homologyOneQuotientToAbelianization X x) =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro q
  induction q using QuotientAddGroup.induction_on with
  | _ z =>
      exact
        fundamentalGroupAbelianizationConcreteHomologyOneAddHom_inverse_mk
          X x z

/-- The concrete cycles-modulo-boundaries form of the degree-one
Hurewicz equivalence. -/
noncomputable def fundamentalGroupAbelianizationConcreteHomologyOneAddEquiv
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    Additive (Abelianization (End (SSet.FundamentalGroupoid.mk x))) ≃+
      integralHomologyOneQuotient X where
  toFun := fundamentalGroupAbelianizationConcreteHomologyOneAddHom X x
  invFun := homologyOneQuotientToAbelianization X x
  left_inv a := by
    have h := DFunLike.congr_fun
      (homologyOneQuotientToAbelianization_comp_forward X x) a
    exact h
  right_inv a := by
    have h := DFunLike.congr_fun
      (fundamentalGroupAbelianizationConcreteHomologyOneAddHom_comp_inverse
        X x) a
    exact h
  map_add' a b := by simp

/-- For a connected simplicial set, integral simplicial homology in degree
one is canonically isomorphic to the additive abelianization of the based
simplicial fundamental group. -/
noncomputable def fundamentalGroupAbelianizationHomologyOneIso
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    AddCommGrpCat.of
        (Additive
          (Abelianization
            (End (SSet.FundamentalGroupoid.mk x)))) ≅
      X.homology
        (AlgebraicTopology.singularIntegralCoefficients :
          AddCommGrpCat.{u}) 1 :=
  (fundamentalGroupAbelianizationConcreteHomologyOneAddEquiv X x).toAddCommGrpIso ≪≫
    (homologyOneConcreteQuotientIso X).symm

/-- The hom of the degree-one Hurewicz Iso is the forward map already
constructed independently of connectedness. -/
@[simp]
theorem fundamentalGroupAbelianizationHomologyOneIso_hom
    (X : SSet.{u}) [X.IsConnected] (x : X _⦋0⦌) :
    (fundamentalGroupAbelianizationHomologyOneIso X x).hom =
      AddCommGrpCat.ofHom
        (fundamentalGroupAbelianizationHomologyOneHom X x).toAdditive := by
  ext q
  rcases q with ⟨q⟩
  rfl

end SSet

end

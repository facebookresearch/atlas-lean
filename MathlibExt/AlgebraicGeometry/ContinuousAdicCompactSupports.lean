/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
public import MathlibExt.AlgebraicGeometry.EllAdicReductionComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Compactly supported cohomology through a compactification

For a scheme `X` over a field `k` with a compactification `c`: an open immersion `j` of `X` into a
proper `k`-scheme `Y` whose complement is the image of a closed immersion `i : Z → Y`, the
compact-support coefficient sheaf of a sheaf `F` on `Y` is the kernel of the unit
`F → i_* i^* F` on the small pro-étale site. This is `j_! j^* F` (Bhatt–Scholze, Lemma 6.1.11):
for a quasi-compact open immersion `j`, the sequence `0 → j_! j^* F → F → i_* i^* F → 0` of
sheaves on the pro-étale site is exact (Stacks 09AH), and `j` is quasi-compact here since `Y`,
proper over a field, is noetherian. Its cohomology `H^n(Y, j_! j^* F)` is the compactly supported
cohomology `H^n_c(X, j^* F)` of Bhatt–Scholze, Definition 6.7.6 (`RΓ_c(X, K) = RΓ(Y, j_! K)`, with
`j_!` exact on the pro-étale site, applied to the sheaf `K = j^* F`). This is not the derived
functor of `G ↦ Γ(Y, j_! G)` on sheaves on `X`, which differs in general (Bhatt–Scholze,
Remark 6.7.8): here `RΓ(Y, -)` is applied to the single sheaf `j_! j^* F`. Taking kernels in the
functor category makes the construction functorial in the coefficients.

For continuous coefficients `ℤ_ℓ` and `ℤ/ℓ^(r+1)`, the reductions induce maps of compactly
supported cohomology, compatible with the transitions; this gives a map to the inverse limit.

References: Stacks Project, Tags 09AH, 03UT and 09BT; Bhatt--Scholze,
The pro-étale topology for schemes, Lemma 6.1.11, Definition 6.7.6, Remark 6.7.8 and §6.8.
-/

namespace MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.EllAdicCohomology
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

universe u

/-- Abelian sheaves on the small pro-étale site of `X`. -/
abbrev AdicAbelianSheaf (X : Scheme.{u}) := Sheaf (ProEt.topology X) Ab.{u + 1}

abbrev abelianPushforward {Y X : Scheme.{u}} (f : Y ⟶ X) :
    AdicAbelianSheaf Y ⥤ AdicAbelianSheaf X :=
  (baseChange f).sheafPushforwardContinuous Ab.{u + 1}
    (ProEt.topology X) (ProEt.topology Y)

abbrev abelianPullback {Y X : Scheme.{u}} (f : Y ⟶ X) :
    AdicAbelianSheaf X ⥤ AdicAbelianSheaf Y :=
  Functor.sheafPullbackConstruction.sheafPullback (baseChange f) Ab.{u + 1}
    (ProEt.topology X) (ProEt.topology Y)

def abelianAdjunction {Y X : Scheme.{u}} (f : Y ⟶ X) :
    abelianPullback f ⊣ abelianPushforward f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The kernel of the unit `F → i_* i^* F` of the inverse and direct image adjunction along `i`. -/
def boundaryKernelFunctor {Z X : Scheme.{u}} (i : Z ⟶ X) :
    AdicAbelianSheaf X ⥤ AdicAbelianSheaf X :=
  kernel (abelianAdjunction i).unit

/-- A compactification of `X` over `k`: an open immersion of `X` into a proper `k`-scheme whose
complement is the image of a closed immersion. -/
structure ClosedCompactification {k : Type u} [Field k] (X : Over (Spec (.of k))) where
  /-- The proper `k`-scheme containing `X`. -/
  ambient : Over (Spec (.of k))
  /-- The open immersion of `X`. -/
  openMap : X ⟶ ambient
  /-- The boundary. -/
  boundary : Scheme.{u}
  /-- The closed immersion of the boundary. -/
  closedMap : boundary ⟶ ambient.left
  proper : IsProper ambient.hom
  openImmersion : IsOpenImmersion openMap.left
  closedImmersion : IsClosedImmersion closedMap
  /-- `X` is the complement of the boundary. -/
  complement : Set.range openMap.left.base = (Set.range closedMap.base)ᶜ

attribute [instance] ClosedCompactification.proper ClosedCompactification.openImmersion
  ClosedCompactification.closedImmersion

/-- The sheaf `C(-, A)` on the compactification, lifted to the universe of the site. -/
abbrev actualCoefficient {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : AdicAbelianSheaf c.ambient.left :=
  (coefficientLift c.ambient.left).obj (coefficientSheaf c.ambient.left A)

/-- The compact-support coefficient sheaf `j_! j^* C(-, A)`. -/
abbrev compactSupportCoefficient {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] : AdicAbelianSheaf c.ambient.left :=
  (boundaryKernelFunctor c.closedMap).obj (actualCoefficient c A)

/-- Compactly supported cohomology of `X` with coefficients `A`. -/
abbrev compactSupportCohomology {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) (A : Type) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] (n : ℕ) :=
  (compactSupportCoefficient c A).H n

/-- The map of compact-support coefficient sheaves induced by a coefficient map. -/
def compactCoefficientMap {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (c : ClosedCompactification X) {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [AddCommGroup A] [AddCommGroup B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    (f : A →ₜ+ B) : compactSupportCoefficient c A ⟶ compactSupportCoefficient c B :=
  (boundaryKernelFunctor c.closedMap).map
    ((coefficientLift c.ambient.left).map (coefficientMap c.ambient.left f))

variable (ell : ℕ) [Fact ell.Prime] [ReductionMaps ell]

variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
  (c : ClosedCompactification X) (n : ℕ)

/-- Compactly supported cohomology with coefficients `ℤ_ℓ`. -/
abbrev integralCompactSupport := compactSupportCohomology c ℤ_[ell] n

/-- Compactly supported cohomology with coefficients `ℤ/ℓ^(r+1)`. -/
abbrev finiteCompactSupport (r : ℕ) :=
  compactSupportCohomology c (ZMod (ell ^ (r + 1))) n

/-- The transition induced by the quotient `ℤ/ℓ^(r+2) → ℤ/ℓ^(r+1)`. -/
def compactTransition (r : ℕ) : finiteCompactSupport ell c n (r + 1) →+
    finiteCompactSupport ell c n r :=
  Sheaf.H.map (compactCoefficientMap c (ReductionMaps.step (ell := ell) r)) n

/-- Reduction modulo `ℓ^(r+1)` of compactly supported cohomology. -/
def compactReduction (r : ℕ) : integralCompactSupport ell c n →+
    finiteCompactSupport ell c n r :=
  Sheaf.H.map (compactCoefficientMap c (ReductionMaps.red (ell := ell) r)) n

/-- The reductions are compatible with the transitions. -/
theorem compactReductionsCommute (r : ℕ) (x : integralCompactSupport ell c n) :
    compactTransition ell c n r (compactReduction ell c n (r + 1) x) =
      compactReduction ell c n r x := by
  have hg : globalCoefficientMap (ReductionMaps.red (ell := ell) (r + 1)) ≫
      globalCoefficientMap (ReductionMaps.step (ell := ell) r) =
        globalCoefficientMap (ReductionMaps.red (ell := ell) r) := by
    ext U s
    change C(U.unop, ℤ_[ell]) at s
    change (ReductionMaps.step (ell := ell) r).toContinuousMap.comp
        ((ReductionMaps.red (ell := ell) (r + 1)).toContinuousMap.comp s) =
      (ReductionMaps.red (ell := ell) r).toContinuousMap.comp s
    apply ContinuousMap.ext
    intro y
    exact ReductionMaps.comp r (s y)
  have hc : coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) (r + 1)) ≫
      coefficientMap c.ambient.left (ReductionMaps.step (ell := ell) r) =
        coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) r) := by
    change (coefficientPushforward c.ambient.left).map _ ≫
      (coefficientPushforward c.ambient.left).map _ =
        (coefficientPushforward c.ambient.left).map _
    rw [← CategoryTheory.Functor.map_comp, hg]
  have hl : (coefficientLift c.ambient.left).map
      (coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) (r + 1))) ≫
        (coefficientLift c.ambient.left).map
          (coefficientMap c.ambient.left (ReductionMaps.step (ell := ell) r)) =
      (coefficientLift c.ambient.left).map
        (coefficientMap c.ambient.left (ReductionMaps.red (ell := ell) r)) := by
    rw [← CategoryTheory.Functor.map_comp, hc]
  have hk : compactCoefficientMap c (ReductionMaps.red (ell := ell) (r + 1)) ≫
      compactCoefficientMap c (ReductionMaps.step (ell := ell) r) =
        compactCoefficientMap c (ReductionMaps.red (ell := ell) r) := by
    change (boundaryKernelFunctor c.closedMap).map _ ≫
      (boundaryKernelFunctor c.closedMap).map _ =
        (boundaryKernelFunctor c.closedMap).map _
    rw [← CategoryTheory.Functor.map_comp, hl]
  exact (Sheaf.H.map_comp_apply _ _ x).symm.trans
    (congrArg (fun f ↦ Sheaf.H.map f n x) hk)

/-- The inverse limit of finite-level compactly supported cohomology, as compatible families. -/
def compactFiniteLimit : AddSubgroup (∀ r : ℕ, finiteCompactSupport ell c n r) where
  carrier := {a | ∀ r, compactTransition ell c n r (a (r + 1)) = a r}
  zero_mem' r := map_zero _
  add_mem' ha hb r := by simp [ha r, hb r]
  neg_mem' ha r := by simp [ha r]

/-- The map from integral compactly supported cohomology to the inverse limit. -/
def compactSupportLimitComparison : integralCompactSupport ell c n →+
    compactFiniteLimit ell c n where
  toFun x := ⟨fun r ↦ compactReduction ell c n r x,
    fun r ↦ compactReductionsCommute ell c n r x⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' x y := Subtype.ext (funext fun _ ↦ map_add _ x y)

end MathlibExt.AlgebraicGeometry.ContinuousAdicCompactSupports

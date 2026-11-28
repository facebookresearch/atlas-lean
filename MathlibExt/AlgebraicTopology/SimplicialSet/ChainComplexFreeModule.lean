/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import MathlibExt.Algebra.Category.ModuleCat.FinsuppCofan
public import Mathlib.SetTheory.Cardinal.UnivLE
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.ULift

/-!
# Simplicial chain modules in free coordinates

Let R be an arbitrary ring and X a simplicial set. In degree n, chains with coefficient module Q
are the direct sum of copies of Q over all n-simplices, including degenerate simplices. The
simplex cofan injections identify with the direct-sum injections.

For R in universe u and X in w, a copy of R in max(u,w) gives free coordinates as finitely
supported R-valued functions on X_n. Under the stated bound that every w-type has a
representative in u, the coefficient R itself instead gives free coordinates on a representative
of X_n in u. When R,X already lie in u, the indices are X_n itself. In each form the simplex
injection gives its basis vector, and a simplicial map pushes coefficients forward by summing
over fibers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped DirectSum

universe u w

namespace SSet

/-- Let R be a ring in u, X a simplicial set in w and Q an R-module in max(u,w). For n∈ℕ, this is
the canonical degree-object isomorphism C_n(X;Q)≅⨁_{x∈X_n}Q. It compares the simplex-indexed
chain coproduct with the direct-sum coproduct, and Q is arbitrary. -/
noncomputable def chainComplexDirectSumIso
    {R : Type u} [Ring R] (X : SSet.{w})
    (Q : ModuleCat.{max u w} R) (n : ℕ) :
    (X.chainComplex Q).X n ≅
      (ModuleCat.of R (⨁ _ : X _⦋n⦌, Q) : ModuleCat.{max u w} R) := by
  classical
  let Z : X _⦋n⦌ → ModuleCat.{max u w} R := fun _ => Q
  exact
    (colimit.isoColimitCocone
      ⟨X.chainComplexXCofan Q n, X.isColimitChainComplexXCofan Q n⟩).symm ≪≫
        ModuleCat.coprodIsoDirectSum Z

open Classical in
/-- For a ring R in u, X in w, coefficient Q in max(u,w), n∈ℕ and x∈X_n, the simplex injection
Q→C_n(X;Q) followed by the direct-sum comparison is the direct-sum injection into the
x-coordinate. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexDirectSumIso_hom
    {R : Type u} [Ring R] (X : SSet.{w})
    (Q : ModuleCat.{max u w} R)
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := Q) x ≫
      (chainComplexDirectSumIso X Q n).hom =
        ModuleCat.ofHom (DirectSum.lof R (X _⦋n⦌) (fun _ => Q) x) := by
  classical
  let Z : X _⦋n⦌ → ModuleCat.{max u w} R := fun _ => Q
  let c : ColimitCocone (Discrete.functor Z) :=
    ⟨X.chainComplexXCofan Q n, X.isColimitChainComplexXCofan Q n⟩
  change X.ιChainComplex x ≫
      ((colimit.isoColimitCocone c).symm ≪≫
        ModuleCat.coprodIsoDirectSum Z).hom = _
  change c.cocone.ι.app ⟨x⟩ ≫
      (colimit.isoColimitCocone c).inv ≫
      (ModuleCat.coprodIsoDirectSum Z).hom = _
  exact (colimit.isoColimitCocone_ι_inv_assoc c ⟨x⟩
    (ModuleCat.coprodIsoDirectSum Z).hom).trans
      (ModuleCat.ι_coprodIsoDirectSum_hom Z x)

section IndependentUniverses

variable (X : SSet.{w}) (R : Type u) [Ring R]

/-- Let R be a ring in universe u and X a simplicial set in universe w, independently. Put
W=max(u,w) and use the canonical copy R̃ of R as coefficient module in W. For n∈ℕ, this
identifies C_n(X;R̃) with the R-module of finitely supported functions X_n→R in W. Each lifted
coefficient is identified with its scalar in R. -/
noncomputable def chainComplexFreeIsoULift (n : ℕ) :
    (X.chainComplex
      (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)).X n ≅
      (ModuleCat.of R (X _⦋n⦌ →₀ R) : ModuleCat.{max u w} R) := by
  classical
  exact
    chainComplexDirectSumIso X
        (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R) n ≪≫
      (((finsuppLEquivDirectSum R (ULift.{w} R) (X _⦋n⦌)).symm.trans
        (Finsupp.mapRange.linearEquiv
          (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R))).toModuleIso)

/-- Let R be a ring in universe u and X a simplicial set in universe w, independently. Put
W=max(u,w) and use the canonical copy R̃ of R as coefficient module in W. For x∈X_n, the
injection R̃→C_n(X;R̃) followed by the free-coordinate comparison sends r̃ to the finitely
supported function with value r at x and zero elsewhere, where r is the identified scalar of R. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIsoULift_hom
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex
        (R := (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)) x ≫
      (chainComplexFreeIsoULift X R n).hom =
        ModuleCat.ofHom
          ((Finsupp.lsingle x (R := R) (M := R)).comp
            (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R).toLinearMap) := by
  classical
  rw [chainComplexFreeIsoULift, Iso.trans_hom, ← Category.assoc,
    ιChainComplex_comp_chainComplexDirectSumIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (Finsupp.mapRange.linearEquiv
      (ULift.moduleEquiv (R := R) : ULift.{w} R ≃ₗ[R] R))
        ((finsuppLEquivDirectSum R (ULift.{w} R) (X _⦋n⦌)).symm
          (DirectSum.lof R (X _⦋n⦌) (fun _ => ULift.{w} R) x r)) =
      Finsupp.single x r.down
  rw [finsuppLEquivDirectSum_symm_lof]
  simp

/-- Let R be a ring in universe u and X a simplicial set in universe w, independently. Put
W=max(u,w) and use the canonical copy R̃ of R as coefficient module in W. For f:X→Y with Y in w,
the degree-n chain map in free coordinates is the pushforward along f_n:X_n→Y_n. It sends the
basis vector r[x] to r[f_n(x)] and sums coefficients over fibers on an arbitrary finitely
supported function. -/
theorem chainComplexMap_comp_chainComplexFreeIsoULift_hom
    {Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f
        (ModuleCat.of R (ULift.{w} R) : ModuleCat.{max u w} R)).f n ≫
      (chainComplexFreeIsoULift Y R n).hom =
        (chainComplexFreeIsoULift X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIsoULift_hom]
  rw [← Category.assoc,
    ιChainComplex_comp_chainComplexFreeIsoULift_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp

end IndependentUniverses

section ShrinkUniverses

private theorem shrinkCoproducts
    (R : Type u) [Ring R] [UnivLE.{w, u}] : HasCoproducts.{w} (ModuleCat.{u} R) := by
  intro I
  exact HasColimitsOfShape.of_small.{u, u} (ModuleCat.{u} R) (Discrete I)

attribute [local instance] shrinkCoproducts

variable (X : SSet.{w}) (R : Type u) [Ring R] [UnivLE.{w, u}]

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For n∈ℕ, C_n(X;R)≅(I_n→₀R) in R-modules with carrier in u.
The source and coefficients retain R itself; the universe hypothesis supplies the representative
simplex index. -/
def chainComplexFreeIsoShrink (n : ℕ) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ≅
      (ModuleCat.of R (Shrink.{u} (X _⦋n⦌) →₀ R) : ModuleCat.{u} R) := by
  classical
  let I := X _⦋n⦌
  let J := Shrink.{u} I
  let j : I ≃ J := equivShrink I
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let cJ : Cofan (fun _ : J => A) := ModuleCat.finsuppCofan R R J
  let hJ : IsColimit cJ := ModuleCat.finsuppCofanIsColimit R R J
  let cI : Cofan (fun _ : I => A) := Cofan.mk cJ.pt (fun x => cJ.inj (j x))
  let hI : IsColimit cI := (Cofan.isColimitEquivOfEquiv j cJ) hJ
  let hX := X.isColimitChainComplexXCofan A n
  exact hX.coconePointUniqueUpToIso hI

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For x∈X_n, the injection R→C_n(X;R) followed by the
comparison sends r to r[e_n(x)] in the finitely supported function module on I_n. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIsoShrink_hom (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x ≫
      (chainComplexFreeIsoShrink X R n).hom =
        ModuleCat.ofHom
          (Finsupp.lsingle (equivShrink (X _⦋n⦌) x) (R := R) (M := R)) := by
  classical
  let I := X _⦋n⦌
  let J := Shrink.{u} I
  let j : I ≃ J := equivShrink I
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let cJ : Cofan (fun _ : J => A) := ModuleCat.finsuppCofan R R J
  let hJ : IsColimit cJ := ModuleCat.finsuppCofanIsColimit R R J
  let cI : Cofan (fun _ : I => A) := Cofan.mk cJ.pt (fun y => cJ.inj (j y))
  let hI : IsColimit cI := (Cofan.isColimitEquivOfEquiv j cJ) hJ
  let hX := X.isColimitChainComplexXCofan A n
  let e := hX.coconePointUniqueUpToIso hI
  have h : X.ιChainComplex (R := A) x ≫ e.hom = cI.inj x :=
    hX.comp_coconePointUniqueUpToIso_hom hI (Discrete.mk x)
  with_unfolding_all exact h

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For x∈X_n, the inverse of C_n(X;R)≅(I_n→₀R) sends the vector
r[e_n(x)] to the simplex injection of r at x. The equality holds as the full linear basis-vector
map from R. -/
@[reassoc]
theorem chainComplexFreeIsoShrink_inv_single (n : ℕ) (x : X _⦋n⦌) :
    ModuleCat.ofHom
        (Finsupp.lsingle (equivShrink (X _⦋n⦌) x) (R := R) (M := R)) ≫
        (chainComplexFreeIsoShrink X R n).inv =
      X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x := by
  let e := chainComplexFreeIsoShrink X R n
  let i := X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x
  have h := ιChainComplex_comp_chainComplexFreeIsoShrink_hom X R n x
  exact (congrArg (fun f => f ≫ e.inv) h).symm.trans
    ((Category.assoc i e.hom e.inv).trans
      ((congrArg (fun f => i ≫ f) e.hom_inv_id).trans (Category.comp_id i)))

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For x∈X_n, this coefficient map C_n(X;R)→R is the
free-coordinate comparison followed by evaluation at e_n(x). It extracts the scalar coefficient
of the given simplex. -/
def chainComplexCoefficientShrink (n : ℕ) (x : X _⦋n⦌) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ⟶
      (ModuleCat.of R R : ModuleCat.{u} R) :=
  (chainComplexFreeIsoShrink X R n).hom ≫
    ModuleCat.ofHom (Finsupp.lapply (equivShrink (X _⦋n⦌) x))

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For a∈C_n(X;R) and x∈X_n, its scalar coefficient is the value
of the free-coordinate image of a at e_n(x). -/
theorem chainComplexCoefficientShrink_apply (n : ℕ) (x : X _⦋n⦌)
    (a : (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n) :
    (chainComplexCoefficientShrink X R n x).hom a =
      ((chainComplexFreeIsoShrink X R n).hom.hom a) (equivShrink (X _⦋n⦌) x) := rfl

open Classical in
/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For x,y∈X_n, the injection at y followed by the coefficient
at x is id_R if y=x and zero otherwise. This identifies the coefficient maps on every simplex
basis injection. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexCoefficientShrink (n : ℕ) (x y : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) y ≫
        chainComplexCoefficientShrink X R n x =
      if y = x then 𝟙 (ModuleCat.of R R : ModuleCat.{u} R) else 0 := by
  classical
  let I := X _⦋n⦌
  let A : ModuleCat.{u} R := ModuleCat.of R R
  let e := chainComplexFreeIsoShrink X R n
  let i := X.ιChainComplex (R := A) y
  let v : A ⟶ (ModuleCat.of R (Shrink.{u} I →₀ R) : ModuleCat.{u} R) :=
    ModuleCat.ofHom (Finsupp.lsingle (equivShrink I y))
  let ev : (ModuleCat.of R (Shrink.{u} I →₀ R) : ModuleCat.{u} R) ⟶ A :=
    ModuleCat.ofHom (Finsupp.lapply (equivShrink I x))
  have hi : i ≫ e.hom = v := ιChainComplex_comp_chainComplexFreeIsoShrink_hom X R n y
  have hLeft : i ≫ chainComplexCoefficientShrink X R n x = v ≫ ev := by
    change i ≫ (e.hom ≫ ev) = v ≫ ev
    exact (Category.assoc i e.hom ev).symm.trans (congrArg (fun f => f ≫ ev) hi)
  have hEval : v ≫ ev = if y = x then 𝟙 A else 0 := by
    by_cases h : y = x
    · have hValue : v ≫ ev = 𝟙 A := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change (Finsupp.single (equivShrink I y) r) (equivShrink I x) = r
        rw [congrArg (equivShrink I) h, Finsupp.single_eq_same]
      exact hValue.trans (ite_eq_left h).symm
    · have hField : equivShrink I y ≠ equivShrink I x := by
        intro hEq
        exact h ((equivShrink I).injective hEq)
      have hValue : v ≫ ev = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        change (Finsupp.single (equivShrink I y) r) (equivShrink I x) = 0
        exact Finsupp.single_eq_of_ne (Ne.symm hField)
      exact hValue.trans (ite_eq_right h).symm
  exact hLeft.trans hEval

/-- Let R be a ring in u and X a simplicial set in w. Assume every type in w admits a representative
in u. For each n choose the canonical representative I_n of X_n with e_n:X_n≅I_n, and retain R
itself as coefficient module in u. For f:X→Y with Y in w, the degree-n map in free coordinates
is pushforward along e_n^Y∘f_n∘(e_n^X)^{-1}. Thus it sends r[e_n^X(x)] to r[e_n^Y(f_nx)] and
sums coefficients over fibers. -/
theorem chainComplexMap_comp_chainComplexFreeIsoShrink_hom
    {Y : SSet.{w}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f (ModuleCat.of R R : ModuleCat.{u} R)).f n ≫
      (chainComplexFreeIsoShrink Y R n).hom =
        (chainComplexFreeIsoShrink X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (fun z : Shrink.{u} (X _⦋n⦌) =>
              equivShrink (Y _⦋n⦌)
                (f.app (op (SimplexCategory.mk n)) ((equivShrink (X _⦋n⦌)).symm z)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIsoShrink_hom]
  rw [← Category.assoc, ιChainComplex_comp_chainComplexFreeIsoShrink_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Finsupp.single (equivShrink (Y _⦋n⦌) (f.app (op (SimplexCategory.mk n)) x)) r =
    Finsupp.mapDomain
      (fun z : Shrink.{u} (X _⦋n⦌) => equivShrink (Y _⦋n⦌)
        (f.app (op (SimplexCategory.mk n)) ((equivShrink (X _⦋n⦌)).symm z)))
      (Finsupp.single (equivShrink (X _⦋n⦌) x) r)
  simp

end ShrinkUniverses

section SameUniverse

variable (X : SSet.{u}) (R : Type u) [Ring R]

/-- Let R be a ring and X a simplicial set in the same universe u, with coefficient module R. For
n∈ℕ, C_n(X;R)≅(X_n→₀R). The indices are all n-simplices and the coefficients are the given
scalar ring. -/
noncomputable def chainComplexFreeIso (n : ℕ) :
    (X.chainComplex (ModuleCat.of R R : ModuleCat.{u} R)).X n ≅
      (ModuleCat.of R (X _⦋n⦌ →₀ R) : ModuleCat.{u} R) := by
  classical
  exact
    chainComplexDirectSumIso X (ModuleCat.of R R : ModuleCat.{u} R) n ≪≫
      (finsuppLEquivDirectSum R R (X _⦋n⦌)).symm.toModuleIso

/-- Let R be a ring and X a simplicial set in the same universe u, with coefficient module R. For
x∈X_n, the injection R→C_n(X;R) followed by the free-coordinate isomorphism is r↦r[x], the
basis-vector map at x. -/
@[reassoc]
theorem ιChainComplex_comp_chainComplexFreeIso_hom
    (n : ℕ) (x : X _⦋n⦌) :
    X.ιChainComplex (R := (ModuleCat.of R R : ModuleCat.{u} R)) x ≫
      (chainComplexFreeIso X R n).hom =
        ModuleCat.ofHom (Finsupp.lsingle x (R := R) (M := R)) := by
  classical
  rw [chainComplexFreeIso, Iso.trans_hom, ← Category.assoc,
    ιChainComplex_comp_chainComplexDirectSumIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (finsuppLEquivDirectSum R R (X _⦋n⦌)).symm
      (DirectSum.lof R (X _⦋n⦌) (fun _ => R) x r) = Finsupp.single x r
  exact finsuppLEquivDirectSum_symm_lof R R (X _⦋n⦌) x r

/-- Let R be a ring and X a simplicial set in the same universe u, with coefficient module R. For a
simplicial map f:X→Y and degree n, the chain map in the free presentations is the linear
pushforward along f_n. Its basis formula is r[x]↦r[f_n(x)], with coefficients summed over
fibers. -/
theorem chainComplexMap_comp_chainComplexFreeIso_hom
    {Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ) :
    (chainComplexMap f (ModuleCat.of R R : ModuleCat.{u} R)).f n ≫
      (chainComplexFreeIso Y R n).hom =
        (chainComplexFreeIso X R n).hom ≫
          ModuleCat.ofHom (Finsupp.lmapDomain R R
            (f.app (Opposite.op (SimplexCategory.mk n)))) := by
  classical
  apply chainComplex_hom_ext
  intro x
  rw [← Category.assoc, ι_chainComplexMap_f,
    ιChainComplex_comp_chainComplexFreeIso_hom]
  rw [← Category.assoc,
    ιChainComplex_comp_chainComplexFreeIso_hom]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  simp

end SameUniverse

end SSet

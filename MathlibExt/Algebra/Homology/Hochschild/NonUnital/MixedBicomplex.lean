/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplex.DegreewiseSplit
public import MathlibExt.Algebra.Homology.ChainComplex.MixedBicomplex
public import MathlibExt.Algebra.Homology.MixedComplex.OfBoundaryHomotopy
public import MathlibExt.Algebra.Homology.MixedComplex.ConnesTail
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.UnitalComparison
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Homology.QuasiIso

import Mathlib.Tactic.Abel

/-!
# Connes operators, mixed totals and cyclic homology

For a commutative ring `k` and a nonunital associative ring with
compatible central `k`-action, cyclic `b,b′,t,N` totalization commutes
with carrier lifting and nonunital algebra maps. Write
`C_n(A)=A ⊗[k] A^⊗n` for regular Hochschild chains.

For unital `A`, insertion of `1_A` gives the Connes operator
`B_n=(1-t_(n+1))s_nN_n`. It satisfies `bB+Bb=0` and `B²=0`,
induces a degree-one operator on Hochschild homology, and gives a
mixed bicomplex with supported cell `C_(q-p)(A)` for `p≤q`,
zero below that region, vertical differential `(-1)^p b`, and
horizontal differential `B`. Its total has degree-`n` terms
`⊕_(2p≤n) C_(n-2p)(A)`.

The translated odd `b′` columns contract by unit insertion, giving
the mixed-to-cyclic comparison and its SBI presentation. The unit-
preserving condition on an algebra map is explicit wherever Connes
and normalization maps use it.

## References

* J.-L. Loday, *Cyclic Homology*, §2.1, for the cyclic and mixed bicomplexes and Connes operator.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits CategoryTheory.Preadditive HomologicalComplex
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

section CyclicTotalLift

universe x

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let `k` be a commutative ring and `A` a nonunital associative
ring with a `k`-module action satisfying
`r•(ab)=(r•a)b=a(r•b)`. Let `C_n(A)=A ⊗[k] A^⊗n` and use
the cyclic `b,b′,t,N` bicomplex. For any extra carrier height `x`, lifting the cyclic total
is canonically isomorphic to totalizing the lifted cyclic bicomplex,
both in module carrier height `max(u,v,x)`. -/
def cyclicTotalLiftIso.{xTL, uTL, vTL} (k : Type uTL) [CommRing k] (A : Type vTL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{xTL, max uTL vTL} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (cyclicTotal k A) ≅
      HomologicalComplex₂.total (((((ModuleCat.uliftFunctor.{xTL, max uTL vTL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) := by
  let U := ModuleCat.uliftFunctor.{xTL, max uTL vTL} k
  let R : HomologicalComplex₂ (ModuleCat.{max uTL vTL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  exact HomologicalComplex₂.functorTotalIso U R

/-- Let `k` be a commutative ring and `A` a nonunital associative
ring with a `k`-module action satisfying
`r•(ab)=(r•a)b=a(r•b)`. Let `C_n(A)=A ⊗[k] A^⊗n` and use
the cyclic `b,b′,t,N` bicomplex. For `p+q=n`, the lifted `(p,q)` cyclic-column injection
followed by the total-lift isomorphism is the corresponding injection
into the total of the lifted bicomplex. -/
@[reassoc]
theorem map_cyclicInclusion_lift.{xIL, uIL, vIL} (k : Type uIL) [CommRing k]
    (A : Type vIL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (p q n : ℕ) (h : p + q = n) :
    (ModuleCat.uliftFunctor.{xIL, max uIL vIL} k).map
      ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) p q n h) ≫
        (cyclicTotalLiftIso.{xIL} k A).hom.f n =
      HomologicalComplex₂.ιTotal (((((ModuleCat.uliftFunctor.{xIL, max uIL vIL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n h := by
  let U := ModuleCat.uliftFunctor.{xIL, max uIL vIL} k
  let R : HomologicalComplex₂ (ModuleCat.{max uIL vIL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
  letI : ∀ m, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  change U.map (R.ιTotal (ComplexShape.down ℕ) p q n h) ≫
      (HomologicalComplex₂.functorTotalIsoComponent U R n).hom = _
  exact HomologicalComplex₂.map_ιTotal_functorTotalIsoComponent_hom U R p q n h

/-- Let `k` be a commutative ring and `A` a nonunital associative
ring with a `k`-module action satisfying
`r•(ab)=(r•a)b=a(r•b)`. Let `C_n(A)=A ⊗[k] A^⊗n` and use
the cyclic `b,b′,t,N` bicomplex. The total-lift comparison preserves the `(p,q)` injection
interpreted as zero when `p+q≠n`, as well as the genuine injection
when `p+q=n`. -/
@[reassoc]
theorem map_cyclicInclusionOrZero_lift.{xZL, uZL, vZL} (k : Type uZL) [CommRing k]
    (A : Type vZL) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (p q n : ℕ) :
    (ModuleCat.uliftFunctor.{xZL, max uZL vZL} k).map
      ((cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p q n) ≫
        (cyclicTotalLiftIso.{xZL} k A).hom.f n =
      HomologicalComplex₂.ιTotalOrZero (((((ModuleCat.uliftFunctor.{xZL, max uZL vZL} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n := by
  let U := ModuleCat.uliftFunctor.{xZL, max uZL vZL} k
  let P : HomologicalComplex₂ (ModuleCat.{max xZL uZL vZL} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  by_cases h : p + q = n
  · rw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) p q n h,
      P.ιTotalOrZero_eq (ComplexShape.down ℕ) p q n h]
    exact map_cyclicInclusion_lift.{xZL} k A p q n h
  · let R : HomologicalComplex₂ (ModuleCat.{max uZL vZL} k)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) := cyclicBicomplex k A
    let T : ChainComplex (ModuleCat.{max xZL uZL vZL} k) ℕ :=
      (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj (cyclicTotal k A)
    let e : T ≅ P.total (ComplexShape.down ℕ) := cyclicTotalLiftIso.{xZL} k A
    let ι : U.obj ((R.X p).X q) ⟶ T.X n :=
      U.map (R.ιTotalOrZero (ComplexShape.down ℕ) p q n)
    let ρ : (P.X p).X q ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) p q n
    have hι : ι = 0 :=
      (congrArg (fun f : (R.X p).X q ⟶ (cyclicTotal k A).X n => U.map f)
        (R.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p q n h)).trans
          (U.map_zero ((R.X p).X q) ((cyclicTotal k A).X n))
    have hρ : ρ = 0 := P.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p q n h
    change ι ≫ e.hom.f n = ρ
    calc
      _ = (0 : U.obj ((R.X p).X q) ⟶ T.X n) ≫ e.hom.f n :=
        congrArg (fun f : U.obj ((R.X p).X q) ⟶ T.X n => f ≫ e.hom.f n) hι
      _ = 0 := zero_comp
      _ = ρ := hρ.symm

section CyclicTotalMap

variable {k A} {B : Type w} [NonUnitalRing B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be a commutative ring and `A` a nonunital associative
ring with a `k`-module action satisfying
`r•(ab)=(r•a)b=a(r•b)`. Let `C_n(A)=A ⊗[k] A^⊗n` and use
the cyclic `b,b′,t,N` bicomplex. For a similarly structured `B` and nonunital algebra map
`f : A →ₙₐ[k] B`, the common-height cyclic total map sends every
`(p,q)` injection to the target injection after applying `f` to all
`q+1` word factors, including zero off-antidiagonal injections. -/
theorem cyclicBicomplexMap_ιTotalOrZero (f : A →ₙₐ[k] B) (p q n : ℕ) :
    HomologicalComplex₂.ιTotalOrZero
      (((((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ) p q n ≫
      (HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)).f n =
        levelMapLift (f : A →ₗ[k] B) q ≫ HomologicalComplex₂.ιTotalOrZero
          (((((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
              (cyclicBicomplex k B))) (ComplexShape.down ℕ) p q n := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
        ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k B)
  let φ : PA ⟶ PB := cyclicBicomplexMap f
  let m := HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  change PA.ιTotalOrZero (ComplexShape.down ℕ) p q n ≫ m.f n =
    levelMapLift (f : A →ₗ[k] B) q ≫ PB.ιTotalOrZero (ComplexShape.down ℕ) p q n
  have hι := HomologicalComplex₂.ιTotalOrZero_map PA PB φ (ComplexShape.down ℕ) p q n
  have hφ : (φ.f p).f q = levelMapLift (f : A →ₗ[k] B) q := cyclicBicomplexMap_f_f f p q
  exact hι.trans (congrArg (fun a => a ≫ PB.ιTotalOrZero (ComplexShape.down ℕ) p q n) hφ)

omit [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B] in
/-- Let `k` be a commutative ring and `A` a nonunital associative
ring with a `k`-module action satisfying
`r•(ab)=(r•a)b=a(r•b)`. Let `C_n(A)=A ⊗[k] A^⊗n` and use
the cyclic `b,b′,t,N` bicomplex. For any `k`-linear map `f : A → B` and insertion vector
`e : A`, the lifted map on word factors commutes with norm followed
by insertion, taking `N_A` then `s_e` to `N_B` then `s_(f(e))`. -/
theorem normInsertWithMapLift_naturality (f : A →ₗ[k] B) (e : A) (n : ℕ) :
    levelMapLift f n ≫
        (ModuleCat.uliftFunctor.{v, max u w} k).map
          (normMap k B n ≫ extraDegeneracyWith k B (f e) n) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map
          (normMap k A n ≫ extraDegeneracyWith k A e n) ≫ levelMapLift f (n + 1) := by
  apply ModuleCat.hom_ext
  ext x
  let z : A ⊗[k] TensorPower k n A := x.down
  let N := TensorPower.consNorm k A n z
  have hN : TensorPower.consNorm k B n (TensorPower.consLevelMap f n z) =
      TensorPower.consLevelMap f n N := (TensorPower.consNorm_natural f n z).symm
  have hs : (extraDegeneracyWith k B (f e) n).hom (TensorPower.consLevelMap f n N) =
      TensorPower.consLevelMap f (n + 1) ((extraDegeneracyWith k A e n).hom N) :=
    (DFunLike.congr_fun (extraDegeneracyWith_naturality f e n) N).symm
  change ULift.up ((extraDegeneracyWith k B (f e) n).hom
      (TensorPower.consNorm k B n (TensorPower.consLevelMap f n z))) =
    ULift.up (TensorPower.consLevelMap f (n + 1) ((extraDegeneracyWith k A e n).hom N))
  exact congrArg ULift.up ((congrArg (extraDegeneracyWith k B (f e) n).hom hN).trans hs)

end CyclicTotalMap

end CyclicTotalLift

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The Connes component induces
`B_* : H_n(C_*(A)) → H_(n+1)(C_*(A))`. -/
def connesBoundaryHomology (n : ℕ) :
    (bComplex k A).homology n ⟶ (bComplex k A).homology (n + 1) :=
  (connesBoundaryHomotopy k A).homologyDegreeMap
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. For any map `x : X → C_n(A)` killed by the outgoing
Hochschild differential, its homology class followed by `B_*`
is the class represented by `x ≫ B_n`. -/
theorem connesBoundaryHomology_representative (n : ℕ) {X : ModuleCat.{max u v} k}
    (x : X ⟶ (bComplex k A).X n)
    (hx : x ≫ (bComplex k A).d n ((ComplexShape.down ℕ).next n) = 0) :
    ((bComplex k A).liftCycles x _ rfl hx ≫ (bComplex k A).homologyπ n) ≫
        connesBoundaryHomology k A n =
      (bComplex k A).liftCycles (x ≫ connesBoundary k A n) n
        ((ComplexShape.down ℕ).next_eq' (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n))
        (by
          simpa only [connesBoundaryHomotopy_hom] using
            ((connesBoundaryHomotopy k A).homologyDegreeMap_isCycle
              (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) x hx)) ≫
        (bComplex k A).homologyπ (n + 1) := by
  simpa only [connesBoundaryHomology, connesBoundaryHomotopy_hom] using
    (connesBoundaryHomotopy k A).homologyDegreeMap_cycle_representative
      (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) x hx

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The induced maps satisfy `B_*^n ≫ B_*^(n+1)=0` on
regular Hochschild homology. -/
theorem connesBoundaryHomology_square (n : ℕ) :
    connesBoundaryHomology k A n ≫ connesBoundaryHomology k A (n + 1) = 0 := by
  apply Homotopy.homologyDegreeMap_comp_eq_zero
    (connesBoundaryHomotopy k A)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))
    (connesBoundaryHomotopy k A)
  simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. Applying the carrier-lift functor to the zero-to-zero
Connes homotopy gives a homotopy on the lifted regular complex,
with its degree-one components the lifted `B_n`. -/
def connesBoundaryHomotopyLift :
    Homotopy
      (0 : ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (bComplex k A) ⟶
          ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj (bComplex k A)) 0 where
  hom := ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
    (connesBoundaryHomotopy k A)).hom
  zero := ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
    (connesBoundaryHomotopy k A)).zero
  comm n := by
    simpa only [Functor.map_zero, HomologicalComplex.zero_f_apply] using
      ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomotopy
        (connesBoundaryHomotopy k A)).comm n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The degree-`n` to degree-`n+1` component of the lifted
Connes homotopy is precisely the image of `B_n` under carrier lifting. -/
@[simp]
theorem connesBoundaryHomotopyLift_hom (n : ℕ) :
    (connesBoundaryHomotopyLift.{u, v, w} k A).hom n (n + 1) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map (connesBoundary k A n) := by
  change (ModuleCat.uliftFunctor.{w, max u v} k).map
    ((connesBoundaryHomotopy k A).hom n (n + 1)) = _
  rw [connesBoundaryHomotopy_hom]

section Naturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be commutative and `A,B` unital rings with compatible
central `k`-module actions, in carriers `v,w`. Let
`f : A →ₙₐ[k] B` be a nonunital algebra map. Lift the two regular
complexes to height `max(u,v,w)` using the opposite carrier heights. The word maps of `f` give the chain map between these
lifted full Hochschild `b`-complexes. -/
def bComplexMapLift (f : A →ₙₐ[k] B) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k A) ⟶
    ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k B) :=
  ChainComplex.ofHom (levelMapLift (f : A →ₗ[k] B)) (fun n => by
    apply ModuleCat.hom_ext
    ext x
    change ULift.up (((bComplex k B).d (n + 1) n).hom
        (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1) x.down)) =
      ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) n
        (((bComplex k A).d (n + 1) n).hom x.down))
    exact congrArg ULift.up (DFunLike.congr_fun (bComplex_d_natural f n) x.down).symm)

/-- Let `k` be commutative and `A,B` unital rings with compatible
central `k`-module actions, in carriers `v,w`. Let
`f : A →ₙₐ[k] B` be a nonunital algebra map. Lift the two regular
complexes to height `max(u,v,w)` using the opposite carrier heights. The degree-`n` component of the lifted chain map is
`levelMapLift(f,n)`, applying `f` to the coefficient and all `n`
algebra factors. -/
@[simp]
theorem bComplexMapLift_f (f : A →ₙₐ[k] B) (n : ℕ) :
    (bComplexMapLift f).f n = levelMapLift (f : A →ₗ[k] B) n := rfl

/-- Let `k` be commutative and `A,B` unital rings with compatible
central `k`-module actions, in carriers `v,w`. Let
`f : A →ₙₐ[k] B` be a nonunital algebra map. Lift the two regular
complexes to height `max(u,v,w)` using the opposite carrier heights. If `f(1_A)=1_B`, the lifted Connes components satisfy
`f_n ≫ B_B,n = B_A,n ≫ f_(n+1)`. -/
theorem bComplexMapLift_boundary (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    (bComplexMapLift f).f n ≫ (connesBoundaryHomotopyLift.{u, w, v} k B).hom n (n + 1) =
      (connesBoundaryHomotopyLift.{u, v, w} k A).hom n (n + 1) ≫
        (bComplexMapLift f).f (n + 1) := by
  rw [connesBoundaryHomotopyLift_hom, connesBoundaryHomotopyLift_hom,
    bComplexMapLift_f, bComplexMapLift_f]
  apply ModuleCat.hom_ext
  ext x
  change ULift.up ((connesBoundary k B n).hom
      (TensorPower.consLevelMap (f : A →ₗ[k] B) n x.down)) =
    ULift.up (TensorPower.consLevelMap (f : A →ₗ[k] B) (n + 1)
      ((connesBoundary k A n).hom x.down))
  exact congrArg ULift.up (DFunLike.congr_fun (connesBoundary_naturality f hOne n) x.down).symm

/-- Let `k` be commutative and `A,B` unital rings with compatible
central `k`-module actions, in carriers `v,w`. Let
`f : A →ₙₐ[k] B` be a nonunital algebra map. Lift the two regular
complexes to height `max(u,v,w)` using the opposite carrier heights. If `f(1_A)=1_B`, the induced homology maps on the lifted
complexes commute with the two degree-one Connes homology operators. -/
theorem connesBoundaryHomology_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    homologyMap (bComplexMapLift f) n ≫
        (connesBoundaryHomotopyLift.{u, w, v} k B).homologyDegreeMap
          (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) =
      (connesBoundaryHomotopyLift.{u, v, w} k A).homologyDegreeMap
          (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n) ≫
        homologyMap (bComplexMapLift f) (n + 1) := by
  apply Homotopy.homologyDegreeMap_naturality_square
    (connesBoundaryHomotopyLift.{u, v, w} k A)
    (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n)
    (connesBoundaryHomotopyLift.{u, w, v} k B) (bComplexMapLift f) (bComplexMapLift f)
  exact bComplexMapLift_boundary f hOne n

end Naturality

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The scalar map `r ↦ r•1_A` gives a `k`-algebra structure
whose induced scalar action is the supplied module action. -/
abbrev regularAlgebra : Algebra k A :=
  Algebra.ofModule (fun r x y => smul_mul_assoc r x y)
    (fun r x y => mul_smul_comm r x y)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. With this algebra structure, the regular complex
`bComplex(k,A)` is canonically isomorphic to the unital coefficient
Hochschild chain complex `C_*(A,A)`. -/
def regularUnitalComplexIso :
    letI := regularAlgebra k A
    bComplex k A ≅ ModuleCat.Algebra.Hochschild.chainComplex k A A := by
  letI := regularAlgebra k A
  let e := complexIsoUnital (k := k) (A := A) (M := A)
  change bComplex k A ≅ ModuleCat.Algebra.Hochschild.chainComplex k A A at e
  exact e

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. Transporting `B_*` across the unital chain comparison
gives `H_n(C_*(A,A)) → H_(n+1)(C_*(A,A))`. -/
def connesBoundaryHomologyUnital (n : ℕ) :
    letI := regularAlgebra k A
    (ModuleCat.Algebra.Hochschild.chainComplex k A A).homology n ⟶
      (ModuleCat.Algebra.Hochschild.chainComplex k A A).homology (n + 1) := by
  letI := regularAlgebra k A
  let e := regularUnitalComplexIso k A
  exact (homologyMapIso e n).inv ≫ connesBoundaryHomology k A n ≫
    (homologyMapIso e (n + 1)).hom

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The full boundary `b` and components `B_n` form a mixed
complex, satisfying `bB+Bb=0` and `B²=0`. -/
def connesMixedComplexModel : MixedComplex (ModuleCat.{max u v} k) :=
  MixedComplex.ofBoundaryHomotopy (bComplex k A) (connesBoundaryHomotopy k A)
    (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The underlying chain complex of the constructed mixed
complex is exactly the regular `b`-complex. -/
@[simp]
theorem connesMixedComplexModel_underlying :
    (connesMixedComplexModel k A).underlying = bComplex k A := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The degree-`n` mixed operator is `B_n`, equivalently norm,
unit insertion, and then `1-t_(n+1)` in that order. -/
@[simp]
theorem connesMixedComplexModel_B (n : ℕ) :
    (connesMixedComplexModel k A).B n = connesBoundary k A n := connesBoundaryHomotopy_hom k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. Its Connes double data gives cells `C_(q-p)(A)` for
`p≤q`, zero cells for `q<p`, vertical differential `(-1)^p b`,
and horizontal differential `B` under the cell identifications. -/
def connesMixedConnesDoubleData : MixedComplex.ConnesDoubleData (connesMixedComplexModel k A) :=
  MixedComplex.ofBoundaryHomotopyConnesDoubleData (bComplex k A) (connesBoundaryHomotopy k A)
    (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The canonical cyclic/SBI data consists of its Connes
bicomplex, the column-zero comparison from `C_*(A)`, and the
chain-level translation by two from the column-zero quotient to
the total. These comparisons have the specified cell components. -/
def connesMixedGenericCyclicData : MixedComplex.GenericMixedCyclicData (connesMixedComplexModel k A) :=
  (connesMixedComplexModel k A).connesCyclicData

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The Connes mixed bicomplex has both shapes `down ℕ`,
with cell `C_(q-p)(A)` for `p≤q` and the mixed boundary maps. -/
def connesMixedBicomplex :
    HomologicalComplex₂ (ModuleCat.{max u v} k) (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (connesMixedConnesDoubleData k A).K

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The bicomplex from the canonical mixed object equals
that constructed directly from the regular `b`-complex, its
Connes zero homotopy, and the component square-zero law. -/
theorem connesMixedBicomplex_eq_original :
    connesMixedBicomplex k A = ChainComplex.mixedBicomplex (bComplex k A) (connesBoundaryHomotopy k A)
      (fun n => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n) := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The model bicomplex of the canonical generic cyclic
data is the Connes mixed bicomplex. -/
theorem connesMixedGenericCyclicData_model_K :
    (connesMixedGenericCyclicData k A).model.K = connesMixedBicomplex k A :=
  MixedComplex.ofBoundaryHomotopy_connesBicomplex (bComplex k A)
    (connesBoundaryHomotopy k A) (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The bottom supported cell `(p,p)` of the mixed bicomplex
is canonically isomorphic to `C_0(A)`. -/
def connesMixedBottomIso (p : ℕ) :
    ((connesMixedBicomplex k A).X p).X p ≅ chainLevel k A A 0 :=
  ChainComplex.mixedColumnIso (bComplex k A) p 0 p (Nat.zero_add p)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. For `p≤q`, the mixed cell `(p,q)` is canonically
identified with `C_(q-p)(A)`. -/
def connesMixedCellIso (p q : ℕ) (hpq : p ≤ q) :
    ((connesMixedBicomplex k A).X p).X q ≅ chainLevel k A A (q - p) :=
  ChainComplex.mixedBicomplexCellIso (bComplex k A) (connesBoundaryHomotopy k A)
    (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r) p q hpq

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The finite-antidiagonal total of the mixed bicomplex
is a nonnegative chain complex, with degree-`n` object
`⊕_(2p≤n) C_(n-2p)(A)`. -/
abbrev connesMixedTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (connesMixedBicomplex k A).total (ComplexShape.down ℕ)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. For `p≤q`, the supported cell identification gives
`C_(q-p)(A) → mixedTotal_(p+q)` as its total summand injection. -/
def connesMixedInclusion (p q : ℕ) (hpq : p ≤ q) :
    chainLevel k A A (q - p) ⟶ (connesMixedTotal k A).X (p + q) :=
  (connesMixedCellIso k A p q hpq).inv ≫
    (connesMixedBicomplex k A).ιTotal (ComplexShape.down ℕ) p q (p + q) rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. In column `p`, multiplying the stored vertical map by
the totalization sign `(-1)^p` gives the ordinary Hochschild
boundary under the translated-column identifications. -/
theorem connesMixedTotal_vertical (p n : ℕ) :
    (ComplexShape.down ℕ).ε p •
        ((connesMixedBicomplex k A).X p).d (n + 1 + p) (n + p) =
      (ChainComplex.mixedColumnIso (bComplex k A) p (n + 1) (n + 1 + p) rfl).hom ≫
        (bComplex k A).d (n + 1) n ≫
          (ChainComplex.mixedColumnIso (bComplex k A) p n (n + p) rfl).inv :=
  ChainComplex.mixedBicomplex_total_vertical (bComplex k A) (connesBoundaryHomotopy k A)
    (fun r => by simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A r) p (n + 1) n
    (n + 1 + p) (n + p) rfl rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. The graded odd family has component `j` the `b′`-complex
translated by `2j+1`; its differential is `-b′` in supported
degrees and its terms vanish below that translation. -/
def connesOddFamily : ChainComplex (GradedObject ℕ (ModuleCat.{max u v} k)) ℕ where
  X n j := (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).X n
  d n m j := (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).d n m
  shape n m h := by
    funext j
    exact (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).shape n m h
  d_comp_d' n m l _ _ := by
    funext j
    exact (ChainComplex.mixedColumn (bPrimeComplex k A) (2 * j + 1)).d_comp_d n m l

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-module action. Write `C_*(A)` for its regular
Hochschild `b`-complex, `t_n` for signed cyclic rotation, and
`N_n=∑_(i=0)^n t_n^i`. The unit insertion `s_n` gives
`B_n=(1-t_(n+1)) ∘ s_n ∘ N_n`. Unit insertion contracts every translated odd `b′`
column, giving a homotopy from identity of the whole graded odd
family to zero. -/
def connesOddFamilyContraction : Homotopy (𝟙 (connesOddFamily k A)) 0 where
  hom n m j :=
    (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).hom n m
  zero n m hnm := by
    funext j
    exact (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).zero n m hnm
  comm n := by
    funext j
    exact (ChainComplex.mixedColumnContraction (bPrimeComplex k A)
      (bPrimeContraction k A) (2 * j + 1)).comm n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. The odd total is the chain complex obtained by the
coproduct of these translated odd columns in each degree. -/
abbrev connesOddTotal : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesOddFamily k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. The column contractions give a homotopy from identity
of `O` to zero. -/
def connesOddContraction : Homotopy (𝟙 (connesOddTotal k A)) 0 where
  hom := ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomotopy
    (connesOddFamilyContraction k A)).hom
  zero := ((GradedObject.total ℕ (ModuleCat.{max u v} k)).mapHomotopy
    (connesOddFamilyContraction k A)).zero
  comm n := by
    let F := GradedObject.total ℕ (ModuleCat.{max u v} k)
    let U := F.mapHomologicalComplex (ComplexShape.down ℕ)
    let K : ChainComplex (GradedObject ℕ (ModuleCat.{max u v} k)) ℕ := connesOddFamily k A
    let L : ChainComplex (ModuleCat.{max u v} k) ℕ := connesOddTotal k A
    let H : Homotopy (U.map (𝟙 K)) (U.map (0 : K ⟶ K)) :=
      F.mapHomotopy (connesOddFamilyContraction k A)
    let a : ∀ i j : ℕ, L.X i ⟶ L.X j := H.hom
    have hId : U.map (𝟙 K) = 𝟙 L := U.map_id K
    have hZero : U.map (0 : K ⟶ K) = (0 : L ⟶ L) := U.map_zero K K
    have hIdF : (U.map (𝟙 K)).f n = (𝟙 L : L ⟶ L).f n :=
      congrArg (fun f : L ⟶ L => f.f n) hId
    have hZeroF : (U.map (0 : K ⟶ K)).f n = (0 : L ⟶ L).f n :=
      congrArg (fun f : L ⟶ L => f.f n) hZero
    change (𝟙 L : L ⟶ L).f n = dNext n a + prevD n a + (0 : L ⟶ L).f n
    exact hIdF.symm.trans ((H.comm n).trans
      (congrArg (fun z : L.X n ⟶ L.X n => dNext n a + prevD n a + z) hZeroF))

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. For `r+2j+1=n`, the supported bar term `C_r` has its
coproduct injection `K_(j,r,n) : C_r → O_n`. -/
def connesOddInclusion (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) r n h).inv ≫
    Sigma.ι ((connesOddFamily k A).X n) j

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. Two morphisms `f,g : O_n → X` to any ground module
are equal if `K_(j,r,n) ≫ f = K_(j,r,n) ≫ g` for every
supported pair `r+2j+1=n`. -/
theorem connesOddTotal_hom_ext {X : ModuleCat.{max u v} k} (n : ℕ)
    {f g : (connesOddTotal k A).X n ⟶ X}
    (h : ∀ j r (hr : r + (2 * j + 1) = n),
      connesOddInclusion k A j r n hr ≫ f = connesOddInclusion k A j r n hr ≫ g) :
    f = g := by
  apply Sigma.hom_ext
  intro j
  by_cases hj : 2 * j + 1 ≤ n
  · let r := n - (2 * j + 1)
    have hr : r + (2 * j + 1) = n := Nat.sub_add_cancel hj
    let e : ((connesOddFamily k A).X n) j ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) r n hr
    let ι : ((connesOddFamily k A).X n) j ⟶ (connesOddTotal k A).X n :=
      CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X n) j
    apply (cancel_epi e.inv).1
    have hh : (e.inv ≫ ι) ≫ f = (e.inv ≫ ι) ≫ g := h j r hr
    change e.inv ≫ (ι ≫ f) = e.inv ≫ (ι ≫ g)
    exact (Category.assoc e.inv ι f).symm.trans (hh.trans (Category.assoc e.inv ι g))
  · exact (ChainComplex.mixedColumn_isZero (bPrimeComplex k A) (2 * j + 1) n
      (by omega)).eq_of_src _ _

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. For `(r+1)+2j+1=n` and `r+2j+1=m`, the injection
intertwines the differential by
`K_(j,r+1,n) ≫ d_O(n,m) = -b′_(r+1,r) ≫ K_(j,r,m)`. -/
theorem connesOddInclusion_d (j r n m : ℕ)
    (hn : (r + 1) + (2 * j + 1) = n) (hm : r + (2 * j + 1) = m) :
    connesOddInclusion k A j (r + 1) n hn ≫ (connesOddTotal k A).d n m =
      -(bPrimeComplex k A).d (r + 1) r ≫ connesOddInclusion k A j r m hm := by
  let K := bPrimeComplex k A
  let T := connesOddTotal k A
  let e₁ : ((connesOddFamily k A).X n) j ≅ chainLevel k A A (r + 1) :=
    ChainComplex.mixedColumnIso K (2 * j + 1) (r + 1) n hn
  let e₀ : ((connesOddFamily k A).X m) j ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso K (2 * j + 1) r m hm
  let ι₁ : ((connesOddFamily k A).X n) j ⟶ T.X n :=
    CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X n) j
  let ι₀ : ((connesOddFamily k A).X m) j ⟶ T.X m :=
    CategoryTheory.Limits.Sigma.ι ((connesOddFamily k A).X m) j
  let δ : ∀ a : ℕ, ((connesOddFamily k A).X n) a ⟶ ((connesOddFamily k A).X m) a :=
    (connesOddFamily k A).d n m
  let v : ((connesOddFamily k A).X n) j ⟶ ((connesOddFamily k A).X m) j := δ j
  let D : T.X n ⟶ T.X m := T.d n m
  let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := K.d (r + 1) r
  have hι : ι₁ ≫ D = v ≫ ι₀ := CategoryTheory.Limits.Sigma.ι_map δ j
  have hOdd : Odd (2 * j + 1) := ⟨j, by omega⟩
  have hv : v = e₁.hom ≫ (-d) ≫ e₀.inv := by
    have hD : v = e₁.hom ≫ (((-1 : ℤˣ) ^ (2 * j + 1)) • d) ≫ e₀.inv := by
      change (ChainComplex.mixedColumn K (2 * j + 1)).d n m = _
      exact ChainComplex.mixedColumn_d_eq K (2 * j + 1) (r + 1) r n m hn hm
    have hsign : ((-1 : ℤˣ) ^ (2 * j + 1)) • d = -d := by
      erw [hOdd.neg_one_pow]
      simp only [Units.neg_smul, one_smul]
    exact hD.trans (congrArg (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A r =>
      e₁.hom ≫ f ≫ e₀.inv) hsign)
  change (e₁.inv ≫ ι₁) ≫ D = -(d ≫ e₀.inv ≫ ι₀)
  calc
    _ = e₁.inv ≫ (ι₁ ≫ D) := Category.assoc _ _ _
    _ = e₁.inv ≫ (v ≫ ι₀) :=
      congrArg (fun f : ((connesOddFamily k A).X n) j ⟶ T.X m => e₁.inv ≫ f) hι
    _ = e₁.inv ≫ ((e₁.hom ≫ (-d) ≫ e₀.inv) ≫ ι₀) :=
      congrArg (fun f : ((connesOddFamily k A).X n) j ⟶ ((connesOddFamily k A).X m) j =>
        e₁.inv ≫ f ≫ ι₀) hv
    _ = -(d ≫ e₀.inv ≫ ι₀) := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.neg_comp, Preadditive.comp_neg]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `T` be the mixed total, with
`T_n=⊕_(2p+r=n) C_r` and injections `J_(p,r,n)`. For `2p+r=n`, the regular term `C_r` has its
mixed-total injection `J_(p,r,n) : C_r → T_n`. -/
def mixedLevelInclusion (p r n : ℕ) (h : 2 * p + r = n) :
    chainLevel k A A r ⟶ (connesMixedTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (connesMixedBicomplex k A).ιTotal (ComplexShape.down ℕ) p (r + p) n (by
      change p + (r + p) = n
      omega)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `T` be the mixed total, with
`T_n=⊕_(2p+r=n) C_r` and injections `J_(p,r,n)`. The degree-indexed mixed injection `J_(p,r,n)` is the
supported injection when `2p+r=n`, and zero otherwise. -/
def mixedLevelInclusionOrZero (p r n : ℕ) :
    chainLevel k A A r ⟶ (connesMixedTotal k A).X n :=
  (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (connesMixedBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p (r + p) n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `T` be the mixed total, with
`T_n=⊕_(2p+r=n) C_r` and injections `J_(p,r,n)`. When `2p+r=n`, the zero-extended mixed injection equals
the supported summand injection. -/
theorem mixedLevelInclusionOrZero_eq (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusionOrZero k A p r n = mixedLevelInclusion k A p r n h := by
  unfold mixedLevelInclusionOrZero mixedLevelInclusion
  erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
    change p + (r + p) = n
    omega)]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `T` be the mixed total, with
`T_n=⊕_(2p+r=n) C_r` and injections `J_(p,r,n)`. Two morphisms `f,g : T_n → X` are equal when their
composites with every `J_(p,r,n)` for `2p+r=n` are equal. -/
theorem connesMixedTotal_hom_ext {X : ModuleCat.{max u v} k} (n : ℕ)
    {f g : (connesMixedTotal k A).X n ⟶ X}
    (h : ∀ p r (hr : 2 * p + r = n),
      mixedLevelInclusion k A p r n hr ≫ f = mixedLevelInclusion k A p r n hr ≫ g) :
    f = g := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hn
  by_cases hpq : p ≤ q
  · obtain ⟨r, hrq⟩ : ∃ r : ℕ, q = r + p :=
      ⟨q - p, (Nat.sub_add_cancel hpq).symm⟩
    subst q
    have hr : 2 * p + r = n := by
      change p + (r + p) = n at hn
      omega
    let B := connesMixedBicomplex k A
    let e : (B.X p).X (r + p) ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
    let i : (B.X p).X (r + p) ⟶ (connesMixedTotal k A).X n :=
      B.ιTotal (ComplexShape.down ℕ) p (r + p) n hn
    apply (cancel_epi e.inv).1
    have hv : (e.inv ≫ i) ≫ f = (e.inv ≫ i) ≫ g := h p r hr
    exact (Category.assoc e.inv i f).symm.trans (hv.trans (Category.assoc e.inv i g))
  · let B := connesMixedBicomplex k A
    have hSquare : ∀ m : ℕ,
        (connesBoundaryHomotopy k A).hom m (m + 1) ≫
          (connesBoundaryHomotopy k A).hom (m + 1) (m + 2) = 0 := fun m => by
      simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A m
    have hZero : IsZero ((B.X p).X q) :=
      ChainComplex.mixedBicomplex_isZero_cell (bComplex k A)
        (connesBoundaryHomotopy k A) hSquare p q (by omega)
    let mf : (B.X p).X q ⟶ X := B.ιTotal (ComplexShape.down ℕ) p q n hn ≫ f
    let mg : (B.X p).X q ⟶ X := B.ιTotal (ComplexShape.down ℕ) p q n hn ≫ g
    exact hZero.eq_of_src mf mg

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. The odd injection `K_(j,r,n)` is defined as zero when
`r+2j+1≠n`, and as the supported coproduct injection otherwise. -/
def connesOddInclusionOrZero (j r n : ℕ) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  if h : r + (2 * j + 1) = n then connesOddInclusion k A j r n h else 0

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `O` be the sum of the odd bar columns translated by `2j+1`,
so `O_n=⊕_(r+2j+1=n) C_r`, with injections `K_(j,r,n)`. For `r+2j+1=n`, the zero-extended odd injection equals
the supported coproduct injection. -/
theorem connesOddInclusionOrZero_eq (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    connesOddInclusionOrZero k A j r n = connesOddInclusion k A j r n h := dif_pos h

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The degreewise even projection `e_n : Z_n → T_n`
sends column `(2p,r)` to `J_(p,r,n)` and kills every odd column. -/
def mixedEvenProjection (n : ℕ) :
    (cyclicTotal k A).X n ⟶ (connesMixedTotal k A).X n :=
  (cyclicBicomplex k A).totalDesc (fun c r hn =>
    if hc : Even c then mixedLevelInclusionOrZero k A (c / 2) r n else 0)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2p+r=n`, the even projection satisfies
`I_(2p,r,n) ≫ e_n = J_(p,r,n)`. -/
theorem mixedEvenProjection_even (p r n : ℕ) (h : 2 * p + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫
        mixedEvenProjection k A n = mixedLevelInclusion k A p r n h := by
  have hp : Even (2 * p) := ⟨p, by omega⟩
  have hDiv : (2 * p) / 2 = p := by omega
  erw [mixedEvenProjection, HomologicalComplex₂.ι_totalDesc]
  simp only [dif_pos hp, if_pos hp, hDiv, mixedLevelInclusionOrZero_eq k A p r n h]
  all_goals first | exact dif_pos hp | exact if_pos hp

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2j+1+r=n`, the even projection vanishes after
`I_(2j+1,r,n)`. -/
theorem mixedEvenProjection_odd (j r n : ℕ) (h : 2 * j + 1 + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * j + 1) r n h ≫
        mixedEvenProjection k A n = 0 := by
  have hj : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  erw [mixedEvenProjection, HomologicalComplex₂.ι_totalDesc]
  exact dif_neg hj

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The degreewise odd section `σ_n : O_n → Z_n`
inserts each odd summand into its cyclic column `2j+1`. -/
def connesOddSection (n : ℕ) : (connesOddTotal k A).X n ⟶ (cyclicTotal k A).X n :=
  Sigma.desc (fun j =>
    if hj : 2 * j + 1 ≤ n then
      (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1)
        (n - (2 * j + 1)) n (Nat.sub_add_cancel hj)).hom ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * j + 1) (n - (2 * j + 1)) n
    else 0)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `r+2j+1=n`, the odd section satisfies
`K_(j,r,n) ≫ σ_n = I_(2j+1,r,n)`. -/
theorem connesOddInclusion_section (j r n : ℕ) (h : r + (2 * j + 1) = n) :
    connesOddInclusion k A j r n h ≫ connesOddSection k A n =
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n := by
  have hj : 2 * j + 1 ≤ n := by omega
  have hr : n - (2 * j + 1) = r := by omega
  subst r
  let F : ℕ → ModuleCat.{max u v} k := (connesOddFamily k A).X n
  let T := connesOddTotal k A
  let e : F j ≅ chainLevel k A A (n - (2 * j + 1)) :=
    ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1)
      (n - (2 * j + 1)) n h
  let ι : F j ⟶ T.X n := Sigma.ι F j
  let s : T.X n ⟶ (cyclicTotal k A).X n := connesOddSection k A n
  let v : chainLevel k A A (n - (2 * j + 1)) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
      (2 * j + 1) (n - (2 * j + 1)) n
  have hι : ι ≫ s = e.hom ≫ v := by
    dsimp only [ι, s, connesOddSection]
    erw [Sigma.ι_desc]
    exact dif_pos hj
  change (e.inv ≫ ι) ≫ s = v
  calc
    (e.inv ≫ ι) ≫ s = e.inv ≫ (ι ≫ s) := Category.assoc _ _ _
    _ = e.inv ≫ (e.hom ≫ v) :=
      congrArg (fun a : F j ⟶ (cyclicTotal k A).X n => e.inv ≫ a) hι
    _ = v := e.inv_hom_id_assoc v


/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The equality `K_(j,r,n) ≫ σ_n = I_(2j+1,r,n)` holds
also for zero-extended injections in every degree `n`. -/
theorem connesOddInclusionOrZero_section (j r n : ℕ) :
    connesOddInclusionOrZero k A j r n ≫ connesOddSection k A n =
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n := by
  by_cases h : r + (2 * j + 1) = n
  · erw [connesOddInclusionOrZero_eq k A j r n h, connesOddInclusion_section]
  · erw [connesOddInclusionOrZero, dif_neg h, zero_comp,
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change 2 * j + 1 + r ≠ n
        omega)] <;> rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The image of mixed coordinate `(p,r)` is
`I_(2p,r,n) + u_r ≫ I_(2p-1,r+1,n)` for `p>0`.
At `p=0` it is `I_(0,r,n)`; off total degree `2p+r=n` it is zero. -/
def mixedToCyclicLevelImage (p r n : ℕ) :
    chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
  let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
    if p = 0 then 0 else
      normMap k A r ≫ extraDegeneracy k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  x + y

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. These coordinate images define the degreewise map
`i_n : T_n → Z_n` by coproduct descent. -/
def mixedToCyclicComponent (n : ℕ) :
    (connesMixedTotal k A).X n ⟶ (cyclicTotal k A).X n :=
  (connesMixedBicomplex k A).totalDesc (fun p q hn =>
    if hpq : p ≤ q then
      (connesMixedCellIso k A p q hpq).hom ≫ mixedToCyclicLevelImage k A p (q - p) n
    else 0)

theorem mixedToCyclicComponent_levelImage (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusion k A p r n h ≫ mixedToCyclicComponent k A n =
      mixedToCyclicLevelImage k A p r n := by
  have hpq : p ≤ r + p := by omega
  have hr : r + p - p = r := Nat.add_sub_cancel r p
  let K := bComplex k A
  let e : ((connesMixedBicomplex k A).X p).X (r + p) ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso K p r (r + p) rfl
  let F : chainLevel k A A r ⟶ (cyclicTotal k A).X n := mixedToCyclicLevelImage k A p r n
  have hCell : (connesMixedCellIso k A p (r + p) hpq).hom ≫
      mixedToCyclicLevelImage k A p (r + p - p) n = e.hom ≫ F := by
    change (ChainComplex.mixedColumnIso K p (r + p - p) (r + p)
      (Nat.sub_add_cancel hpq)).hom ≫ mixedToCyclicLevelImage k A p (r + p - p) n = _
    have hCompare : ∀ (t : ℕ) (ht : t + p = r + p), t = r →
        (ChainComplex.mixedColumnIso K p t (r + p) ht).hom ≫
          mixedToCyclicLevelImage k A p t n = e.hom ≫ F := by
      intro t ht he
      cases he
      rfl
    exact hCompare (r + p - p) (Nat.sub_add_cancel hpq) hr
  unfold mixedLevelInclusion mixedToCyclicComponent
  erw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  calc
    _ = e.inv ≫ ((connesMixedCellIso k A p (r + p) hpq).hom ≫
        mixedToCyclicLevelImage k A p (r + p - p) n) :=
      congrArg (fun f : ((connesMixedBicomplex k A).X p).X (r + p) ⟶ (cyclicTotal k A).X n =>
        e.inv ≫ f) (dite_eq_left hpq)
    _ = e.inv ≫ (e.hom ≫ F) :=
      congrArg (fun f : ((connesMixedBicomplex k A).X p).X (r + p) ⟶ (cyclicTotal k A).X n =>
        e.inv ≫ f) hCell
    _ = F := e.inv_hom_id_assoc F

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2p+r=n`, the map `i_n` takes `J_(p,r,n)` to
its even cyclic coordinate plus the `u_r=s_rN_r` correction in
column `2p-1`; the correction is zero at `p=0`. -/
theorem mixedToCyclicComponent_inclusion (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusion k A p r n h ≫ mixedToCyclicComponent k A n =
      (let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
       let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          normMap k A r ≫ extraDegeneracy k A r ≫
            (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
       x + y) := by
  erw [mixedToCyclicComponent_levelImage]
  by_cases hp : p = 0
  · subst p
    let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * 0) r n
    let i : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * 0 - 1) (r + 1) n
    let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
      normMap k A r ≫ extraDegeneracy k A r ≫ i
    have hi : i = 0 := HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
      change 2 * 0 - 1 + (r + 1) ≠ n
      omega)
    have hy : y = 0 := (Category.assoc (normMap k A r) (extraDegeneracy k A r) i).symm.trans
      ((congrArg (fun f : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n =>
        (normMap k A r ≫ extraDegeneracy k A r) ≫ f) hi).trans comp_zero)
    change x + 0 = x + y
    exact congrArg (fun f : chainLevel k A A r ⟶ (cyclicTotal k A).X n => x + f) hy.symm
  · exact by simp only [mixedToCyclicLevelImage, if_neg hp]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The mixed coordinate image is zero whenever `2p+r≠n`. -/
theorem mixedToCyclicLevelImage_eq_zero (p r n : ℕ) (h : 2 * p + r ≠ n) :
    mixedToCyclicLevelImage k A p r n = 0 := by
  have hz : (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n = 0 :=
    HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h
  by_cases hp : p = 0
  · simp only [mixedToCyclicLevelImage, if_pos hp, hz, add_zero]
    exact zero_add (0 : chainLevel k A A r ⟶ (cyclicTotal k A).X n)
  · have hz' : (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n = 0 :=
      HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change 2 * p - 1 + (r + 1) ≠ n
        omega)
    simp only [mixedToCyclicLevelImage, if_neg hp, hz, hz', comp_zero, add_zero]
    let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let Z := (cyclicTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    have hzero : N ≫ S ≫ (0 : Y ⟶ Z) = 0 :=
      (Category.assoc N S (0 : Y ⟶ Z)).symm.trans comp_zero
    change (0 : X ⟶ Z) + N ≫ S ≫ (0 : Y ⟶ Z) = 0
    exact (congrArg (fun f : X ⟶ Z => (0 : X ⟶ Z) + f) hzero).trans (zero_add 0)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. Composing the zero-extended `J_(p,r,n)` with `i_n`
gives its coordinate image for every `p,r,n`. -/
theorem mixedToCyclicComponent_inclusionOrZero (p r n : ℕ) :
    mixedLevelInclusionOrZero k A p r n ≫ mixedToCyclicComponent k A n =
      mixedToCyclicLevelImage k A p r n := by
  by_cases h : 2 * p + r = n
  · erw [mixedLevelInclusionOrZero_eq k A p r n h, mixedToCyclicComponent_levelImage]
  · have hz : mixedLevelInclusionOrZero k A p r n = 0 := by
      unfold mixedLevelInclusionOrZero
      erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ (by
        change p + (r + p) ≠ n
        omega), comp_zero]
    erw [hz, zero_comp, mixedToCyclicLevelImage_eq_zero k A p r n h]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The image of even cyclic coordinate `(2p,r)` in `O_n`
is `-u_r ≫ K_(p-1,r+1,n)` for `p>0`, and zero at `p=0`. -/
def cyclicToOddEvenImage (p r n : ℕ) :
    chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
  if p = 0 then 0 else
    -(normMap k A r ≫ extraDegeneracy k A r ≫
      connesOddInclusionOrZero k A (p - 1) (r + 1) n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The degreewise projection `π_n : Z_n → O_n`
uses `-s_rN_r` on the preceding odd coordinate of an even column
and identity on each odd column. -/
def cyclicToOddComponent (n : ℕ) :
    (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
  (cyclicBicomplex k A).totalDesc (fun c r hn =>
    if hc : Even c then cyclicToOddEvenImage k A (c / 2) r n
    else connesOddInclusionOrZero k A (c / 2) r n)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2p+r=n`, the projection satisfies
`I_(2p,r,n) ≫ π_n = -u_r ≫ K_(p-1,r+1,n)`, with the
zero-extended right side zero when `p=0`. -/
theorem cyclicToOddComponent_even (p r n : ℕ) (h : 2 * p + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫
        cyclicToOddComponent k A n =
      -(normMap k A r ≫ extraDegeneracy k A r ≫
        connesOddInclusionOrZero k A (p - 1) (r + 1) n) := by
  have hp : Even (2 * p) := ⟨p, by omega⟩
  have hDiv : (2 * p) / 2 = p := by omega
  erw [cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_left hp, hDiv]
  by_cases hp0 : p = 0
  · subst p
    let i : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n :=
      connesOddInclusionOrZero k A (0 - 1) (r + 1) n
    let Y : chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
      normMap k A r ≫ extraDegeneracy k A r ≫ i
    have hi : i = 0 := by
      unfold i connesOddInclusionOrZero
      exact dite_eq_right (by omega)
    have hY : Y = 0 := (Category.assoc (normMap k A r) (extraDegeneracy k A r) i).symm.trans
      ((congrArg (fun f : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n =>
        (normMap k A r ≫ extraDegeneracy k A r) ≫ f) hi).trans comp_zero)
    change (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) = -Y
    exact ((congrArg (fun f : chainLevel k A A r ⟶ (connesOddTotal k A).X n => -f) hY).trans
      neg_zero).symm
  · change (if p = 0 then (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) else
      -(normMap k A r ≫ extraDegeneracy k A r ≫
        connesOddInclusionOrZero k A (p - 1) (r + 1) n)) = _
    exact if_neg hp0

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2j+1+r=n`, the projection satisfies
`I_(2j+1,r,n) ≫ π_n = K_(j,r,n)`. -/
theorem cyclicToOddComponent_odd (j r n : ℕ) (h : 2 * j + 1 + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * j + 1) r n h ≫
        cyclicToOddComponent k A n = connesOddInclusion k A j r n (by omega) := by
  have hj : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  have hDiv : (2 * j + 1) / 2 = j := by omega
  erw [cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_right hj, hDiv]
  exact connesOddInclusionOrZero_eq k A j r n (by omega)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The even coordinate image in the odd quotient is zero
when `2p+r≠n`. -/
theorem cyclicToOddEvenImage_eq_zero (p r n : ℕ) (h : 2 * p + r ≠ n) :
    cyclicToOddEvenImage k A p r n = 0 := by
  by_cases hp : p = 0
  · simp only [cyclicToOddEvenImage, if_pos hp]
  · have hz : connesOddInclusionOrZero k A (p - 1) (r + 1) n = 0 := by
      unfold connesOddInclusionOrZero
      erw [dif_neg (by omega)]
    simp only [cyclicToOddEvenImage, if_neg hp, hz, comp_zero, neg_zero]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The zero-extended even cyclic injection followed by
`π_n` gives its even quotient-coordinate image in every degree. -/
theorem cyclicToOddComponent_evenOrZero (p r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n ≫
        cyclicToOddComponent k A n = cyclicToOddEvenImage k A p r n := by
  by_cases h : 2 * p + r = n
  · have hp : Even (2 * p) := ⟨p, by omega⟩
    have hDiv : (2 * p) / 2 = p := by omega
    erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      cyclicToOddComponent, HomologicalComplex₂.ι_totalDesc, dite_eq_left hp, hDiv]
  · erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp,
      cyclicToOddEvenImage_eq_zero k A p r n h]
    change (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n) = 0
    rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The zero-extended odd cyclic injection followed by
`π_n` is the zero-extended odd quotient injection
`K_(j,r,n)`. -/
theorem cyclicToOddComponent_oddOrZero (j r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n ≫
        cyclicToOddComponent k A n = connesOddInclusionOrZero k A j r n := by
  by_cases h : 2 * j + 1 + r = n
  · erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ h,
      cyclicToOddComponent_odd k A j r n h, connesOddInclusionOrZero_eq k A j r n (by omega)]
  · erw [HomologicalComplex₂.ιTotalOrZero_eq_zero _ _ _ _ _ h, zero_comp]
    have hz : r + (2 * j + 1) ≠ n := by omega
    have hi : connesOddInclusionOrZero k A j r n = 0 := by
      change (if hs : r + (2 * j + 1) = n then connesOddInclusion k A j r n hs else
        (0 : chainLevel k A A r ⟶ (connesOddTotal k A).X n)) = 0
      exact dite_eq_right hz
    exact hi.symm
theorem cyclic_d₁_even (p r m : ℕ) :
    (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) (2 * p) r m =
      if p = 0 then 0 else normMap k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) r m := by
  by_cases hp : p = 0
  · subst p
    erw [if_pos rfl]
    exact (cyclicBicomplex k A).d₁_eq_zero (ComplexShape.down ℕ) 0 r m
      (by simp [ComplexShape.down_Rel])
  · erw [if_neg hp, (cyclicBicomplex k A).d₁_eq' (ComplexShape.down ℕ)
      (show (ComplexShape.down ℕ).Rel (2 * p) (2 * p - 1) from by
        change 2 * p - 1 + 1 = 2 * p
        omega) r m]
    have hc : ¬ Even (2 * p - 1) := by rintro ⟨a, ha⟩; omega
    have hpred : (2 * p - 1) + 1 = 2 * p := by omega
    have hField := cyclicBicomplex_horizontal k A (2 * p - 1) r
    erw [hpred, if_neg hc] at hField
    change (1 : ℤˣ) •
      (((cyclicBicomplex k A).d (2 * p) (2 * p - 1)).f r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) r m) = _
    erw [one_smul, hField] <;> rfl

theorem cyclic_d₁_odd (j r m : ℕ) :
    (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) (2 * j + 1) r m =
      (𝟙 (chainLevel k A A r) - cyclicMap k A r) ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) r m := by
  erw [(cyclicBicomplex k A).d₁_eq' (ComplexShape.down ℕ)
    (show (ComplexShape.down ℕ).Rel (2 * j + 1) (2 * j) from rfl) r m]
  have hc : Even (2 * j) := ⟨j, by omega⟩
  have hField := cyclicBicomplex_horizontal k A (2 * j) r
  erw [if_pos hc] at hField
  change (1 : ℤˣ) • (((cyclicBicomplex k A).d (2 * j + 1) (2 * j)).f r ≫
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) r m) = _
  erw [one_smul, hField] <;> rfl

theorem cyclic_d₂_even (p r m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) (2 * p) (r + 1) m =
      (bComplex k A).d (r + 1) r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r m := by
  erw [(cyclicBicomplex k A).d₂_eq' (ComplexShape.down ℕ) (2 * p)
    (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) m]
  have hp : Even (2 * p) := ⟨p, by omega⟩
  change (ComplexShape.down ℕ).ε (2 * p) •
    (((cyclicBicomplex k A).X (2 * p)).d (r + 1) r ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r m) = _
  erw [ComplexShape.ε_down_ℕ, hp.neg_one_pow, one_smul,
    cyclicBicomplex_vertical, if_pos hp] <;> rfl

theorem cyclic_d₂_odd (j r m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) (2 * j + 1) (r + 1) m =
      -(bPrimeComplex k A).d (r + 1) r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r m := by
  erw [(cyclicBicomplex k A).d₂_eq' (ComplexShape.down ℕ) (2 * j + 1)
    (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) m]
  have hj : Odd (2 * j + 1) := ⟨j, by omega⟩
  have hj' : ¬ Even (2 * j + 1) := by rintro ⟨a, ha⟩; omega
  change (ComplexShape.down ℕ).ε (2 * j + 1) •
    (((cyclicBicomplex k A).X (2 * j + 1)).d (r + 1) r ≫
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r m) = _
  erw [ComplexShape.ε_down_ℕ, hj.neg_one_pow, cyclicBicomplex_vertical, if_neg hj']
  simp only [Units.neg_smul, one_smul, neg_comp] <;> rfl

theorem cyclic_d₂_bottom (c m : ℕ) :
    (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) c 0 m = 0 :=
  (cyclicBicomplex k A).d₂_eq_zero (ComplexShape.down ℕ) c 0 m
    (by simp [ComplexShape.down_Rel])

theorem cyclicInclusion_d (c r n m : ℕ) (h : c + r = n) :
    (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r n h ≫
        (cyclicTotal k A).d n m =
      (cyclicBicomplex k A).d₁ (ComplexShape.down ℕ) c r m +
        (cyclicBicomplex k A).d₂ (ComplexShape.down ℕ) c r m := by
  change (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r n h ≫
    ((cyclicBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
      (cyclicBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

theorem norm_extra_contraction_succ (r : ℕ) :
    (let x : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        (normMap k A (r + 1) ≫ extraDegeneracy k A (r + 1)) ≫
          (bPrimeComplex k A).d (r + 2) (r + 1)
     let y : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        (bComplex k A).d (r + 1) r ≫ normMap k A r ≫ extraDegeneracy k A r
     x + y) = normMap k A (r + 1) := by
  let X₀ := chainLevel k A A r
  let X₁ := chainLevel k A A (r + 1)
  let X₂ := chainLevel k A A (r + 2)
  let N₀ : X₀ ⟶ X₀ := normMap k A r
  let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
  let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
  let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
  let d₀ : X₁ ⟶ X₀ := (bComplex k A).d (r + 1) r
  let d₀' : X₁ ⟶ X₀ := (bPrimeComplex k A).d (r + 1) r
  let d₁' : X₂ ⟶ X₁ := (bPrimeComplex k A).d (r + 2) (r + 1)
  have h := (bPrimeContraction k A).comm (r + 1)
  erw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl),
    prevD_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel (r + 2) (r + 1) from rfl),
    bPrimeContraction_hom, bPrimeContraction_hom] at h
  have hC : 𝟙 X₁ = d₀' ≫ s₀ + s₁ ≫ d₁' := h
  have hSum : s₁ ≫ d₁' + d₀' ≫ s₀ = 𝟙 X₁ :=
    (add_comm (s₁ ≫ d₁') (d₀' ≫ s₀)).trans hC.symm
  have hN : d₀ ≫ N₀ = N₁ ≫ d₀' := (normMap_comp_bPrime_d k A r).symm
  change (N₁ ≫ s₁) ≫ d₁' + d₀ ≫ N₀ ≫ s₀ = N₁
  calc
    _ = N₁ ≫ (s₁ ≫ d₁') + (d₀ ≫ N₀) ≫ s₀ :=
      congrArg₂ (fun f g : X₁ ⟶ X₁ => f + g) (Category.assoc N₁ s₁ d₁')
        (Category.assoc d₀ N₀ s₀).symm
    _ = N₁ ≫ (s₁ ≫ d₁') + (N₁ ≫ d₀') ≫ s₀ :=
      congrArg (fun f : X₁ ⟶ X₀ => N₁ ≫ (s₁ ≫ d₁') + f ≫ s₀) hN
    _ = N₁ ≫ (s₁ ≫ d₁' + d₀' ≫ s₀) :=
      (congrArg (fun f : X₁ ⟶ X₁ => N₁ ≫ (s₁ ≫ d₁') + f)
        (Category.assoc N₁ d₀' s₀)).trans
          (Preadditive.comp_add X₁ X₁ X₁ N₁ (s₁ ≫ d₁') (d₀' ≫ s₀)).symm
    _ = N₁ ≫ 𝟙 X₁ := congrArg (fun f : X₁ ⟶ X₁ => N₁ ≫ f) hSum
    _ = N₁ := Category.comp_id N₁
theorem norm_extra_contraction_bottom :
    (normMap k A 0 ≫ extraDegeneracy k A 0) ≫ (bPrimeComplex k A).d 1 0 =
      normMap k A 0 := by
  let X₀ := chainLevel k A A 0
  let X₁ := chainLevel k A A 1
  let N : X₀ ⟶ X₀ := normMap k A 0
  let s : X₀ ⟶ X₁ := extraDegeneracy k A 0
  let d : X₁ ⟶ X₀ := (bPrimeComplex k A).d 1 0
  have h := (bPrimeContraction k A).comm 0
  erw [HomologicalComplex.id_f, HomologicalComplex.zero_f_apply, add_zero,
    dNext_eq_zero (bPrimeContraction k A).hom 0 (by simp [ComplexShape.down_Rel]),
    prevD_eq (bPrimeContraction k A).hom (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
    bPrimeContraction_hom, zero_add] at h
  have hC : s ≫ d = 𝟙 X₀ := h.symm
  change (N ≫ s) ≫ d = N
  calc
    _ = N ≫ (s ≫ d) := Category.assoc N s d
    _ = N ≫ 𝟙 X₀ := congrArg (fun f : X₀ ⟶ X₀ => N ≫ f) hC
    _ = N := Category.comp_id N
omit [IsScalarTower k A A] [SMulCommClass k A A] in
theorem boundary_comp_norm_extra (r : ℕ) :
    connesBoundary k A r ≫ normMap k A (r + 1) ≫ extraDegeneracy k A (r + 1) = 0 := by
  let X₀ := chainLevel k A A r
  let X₁ := chainLevel k A A (r + 1)
  let X₂ := chainLevel k A A (r + 2)
  let N₀ : X₀ ⟶ X₀ := normMap k A r
  let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
  let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
  let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
  let t : X₁ ⟶ X₁ := 𝟙 X₁ - cyclicMap k A (r + 1)
  let B : X₀ ⟶ X₁ := connesBoundary k A r
  have hB : B = N₀ ≫ s₀ ≫ t := connesBoundary_eq k A r
  have ht : t ≫ N₁ = 0 := oneSubCyclicMap_comp_normMap k A (r + 1)
  change B ≫ N₁ ≫ s₁ = 0
  calc
    _ = (N₀ ≫ s₀ ≫ t) ≫ N₁ ≫ s₁ :=
      congrArg (fun f : X₀ ⟶ X₁ => f ≫ N₁ ≫ s₁) hB
    _ = N₀ ≫ s₀ ≫ (t ≫ N₁) ≫ s₁ := by simp only [Category.assoc]
    _ = N₀ ≫ s₀ ≫ (0 : X₁ ⟶ X₁) ≫ s₁ :=
      congrArg (fun f : X₁ ⟶ X₁ => N₀ ≫ s₀ ≫ f ≫ s₁) ht
    _ = 0 := by simp only [zero_comp, comp_zero]
theorem mixedCoordinateInclusion_eq (p r q n : ℕ) (h : r + p = q) :
    (ChainComplex.mixedColumnIso (bComplex k A) p r q h).inv ≫
        (connesMixedBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) p q n =
      mixedLevelInclusionOrZero k A p r n := by
  subst q
  rfl

theorem mixed_d₁ (p r m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
        (connesMixedBicomplex k A).d₁ (ComplexShape.down ℕ) p (r + p) m =
      if p = 0 then 0 else
        connesBoundary k A r ≫ mixedLevelInclusionOrZero k A (p - 1) (r + 1) m := by
  cases p with
  | zero =>
    erw [if_pos rfl, (connesMixedBicomplex k A).d₁_eq_zero (ComplexShape.down ℕ)
      0 (r + 0) m (by simp [ComplexShape.down_Rel]), comp_zero]
  | succ p =>
    have hField : ((connesMixedBicomplex k A).d (p + 1) p).f (r + (p + 1)) =
        (ChainComplex.mixedColumnIso (bComplex k A) (p + 1) r (r + (p + 1)) rfl).hom ≫
          connesBoundary k A r ≫
            (ChainComplex.mixedColumnIso (bComplex k A) p (r + 1)
              (r + (p + 1)) (by omega)).inv := by
      dsimp only [connesMixedBicomplex, connesMixedConnesDoubleData,
        MixedComplex.ofBoundaryHomotopyConnesDoubleData, ChainComplex.mixedBicomplex]
      erw [ChainComplex.of_d, ChainComplex.mixedHorizontalMap_f,
        ChainComplex.mixedHorizontalComponent_eq _ _ p r (r + (p + 1)) rfl,
        connesBoundaryHomotopy_hom]
    let D := connesMixedBicomplex k A
    let q := r + (p + 1)
    let a : (D.X (p + 1)).X q ≅ chainLevel k A A r :=
      ChainComplex.mixedColumnIso (bComplex k A) (p + 1) r q rfl
    let c : (D.X p).X q ≅ chainLevel k A A (r + 1) :=
      ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) q (by dsimp only [q]; omega)
    let i : (D.X p).X q ⟶ (connesMixedTotal k A).X m :=
      D.ιTotalOrZero (ComplexShape.down ℕ) p q m
    let d : (D.X (p + 1)).X q ⟶ (D.X p).X q := (D.d (p + 1) p).f q
    let B : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := connesBoundary k A r
    have hd : d = a.hom ≫ B ≫ c.inv := hField
    have hD : D.d₁ (ComplexShape.down ℕ) (p + 1) q m = (1 : ℤˣ) • (d ≫ i) :=
      D.d₁_eq' (ComplexShape.down ℕ)
        (by rfl : (ComplexShape.down ℕ).Rel (p + 1) p) q m
    have hi : c.inv ≫ i = mixedLevelInclusionOrZero k A p (r + 1) m :=
      mixedCoordinateInclusion_eq k A p (r + 1) q m (by dsimp only [q]; omega)
    erw [if_neg (Nat.succ_ne_zero p)]
    change a.inv ≫ D.d₁ (ComplexShape.down ℕ) (p + 1) q m = B ≫ _
    calc
      _ = a.inv ≫ ((1 : ℤˣ) • (d ≫ i)) :=
        congrArg (fun f : (D.X (p + 1)).X q ⟶ (connesMixedTotal k A).X m => a.inv ≫ f) hD
      _ = a.inv ≫ (d ≫ i) := by rw [one_smul]
      _ = a.inv ≫ ((a.hom ≫ B ≫ c.inv) ≫ i) :=
        congrArg (fun f : (D.X (p + 1)).X q ⟶ (D.X p).X q => a.inv ≫ (f ≫ i)) hd
      _ = B ≫ (c.inv ≫ i) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = B ≫ mixedLevelInclusionOrZero k A p (r + 1) m :=
        congrArg (fun f : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m => B ≫ f) hi

theorem mixed_d₂_succ (p r m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) (r + 1 + p) rfl).inv ≫
        (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p (r + 1 + p) m =
      (bComplex k A).d (r + 1) r ≫ mixedLevelInclusionOrZero k A p r m := by
  let D := connesMixedBicomplex k A
  let a : (D.X p).X (r + 1 + p) ≅ chainLevel k A A (r + 1) :=
    ChainComplex.mixedColumnIso (bComplex k A) p (r + 1) (r + 1 + p) rfl
  let c : (D.X p).X (r + p) ≅ chainLevel k A A r :=
    ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
  let v : (D.X p).X (r + 1 + p) ⟶ (D.X p).X (r + p) := (D.X p).d (r + 1 + p) (r + p)
  let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := (bComplex k A).d (r + 1) r
  let i : (D.X p).X (r + p) ⟶ (connesMixedTotal k A).X m :=
    D.ιTotalOrZero (ComplexShape.down ℕ) p (r + p) m
  let σ : ℤˣ := (ComplexShape.down ℕ).ε p
  have hD : D.d₂ (ComplexShape.down ℕ) p (r + 1 + p) m = σ • (v ≫ i) :=
    D.d₂_eq' (ComplexShape.down ℕ) p
      (by change r + p + 1 = r + 1 + p; omega) m
  have hv : σ • v = a.hom ≫ d ≫ c.inv := connesMixedTotal_vertical k A p r
  have hi : c.inv ≫ i = mixedLevelInclusionOrZero k A p r m := rfl
  change a.inv ≫ D.d₂ (ComplexShape.down ℕ) p (r + 1 + p) m = d ≫ _
  calc
    _ = a.inv ≫ (σ • (v ≫ i)) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (connesMixedTotal k A).X m => a.inv ≫ f) hD
    _ = a.inv ≫ ((σ • v) ≫ i) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (connesMixedTotal k A).X m => a.inv ≫ f)
        (Linear.units_smul_comp σ v i).symm
    _ = a.inv ≫ ((a.hom ≫ d ≫ c.inv) ≫ i) :=
      congrArg (fun f : (D.X p).X (r + 1 + p) ⟶ (D.X p).X (r + p) => a.inv ≫ (f ≫ i)) hv
    _ = d ≫ (c.inv ≫ i) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = d ≫ mixedLevelInclusionOrZero k A p r m := congrArg (fun f => d ≫ f) hi

theorem mixed_d₂_bottom (p m : ℕ) :
    (ChainComplex.mixedColumnIso (bComplex k A) p 0 p (Nat.zero_add p)).inv ≫
        (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p p m = 0 := by
  by_cases hp : p = 0
  · subst p
    erw [(connesMixedBicomplex k A).d₂_eq_zero (ComplexShape.down ℕ) 0 0 m
      (by simp [ComplexShape.down_Rel]), comp_zero]
  · erw [(connesMixedBicomplex k A).d₂_eq' (ComplexShape.down ℕ) p
      (show (ComplexShape.down ℕ).Rel p (p - 1) from by
        change p - 1 + 1 = p
        omega) m]
    have hd : ((connesMixedBicomplex k A).X p).d p (p - 1) = 0 :=
      (ChainComplex.mixedColumn_isZero (bComplex k A) p (p - 1) (by omega)).eq_of_tgt _ _
    erw [hd, zero_comp, smul_zero, comp_zero]

theorem mixedInclusion_d_succ (p r n m : ℕ) (h : 2 * p + (r + 1) = n) :
    mixedLevelInclusion k A p (r + 1) n h ≫ (connesMixedTotal k A).d n m =
      (let x : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m :=
          if p = 0 then 0 else
            connesBoundary k A (r + 1) ≫ mixedLevelInclusionOrZero k A (p - 1) (r + 2) m
       let y : chainLevel k A A (r + 1) ⟶ (connesMixedTotal k A).X m :=
          (bComplex k A).d (r + 1) r ≫ mixedLevelInclusionOrZero k A p r m
       x + y) := by
  unfold mixedLevelInclusion
  change (_ ≫ _) ≫ ((connesMixedBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
    (connesMixedBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, Category.assoc, Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, mixed_d₁, mixed_d₂_succ]

theorem mixedInclusion_d_bottom (p n m : ℕ) (h : 2 * p + 0 = n) :
    mixedLevelInclusion k A p 0 n h ≫ (connesMixedTotal k A).d n m =
      if p = 0 then 0 else connesBoundary k A 0 ≫
        mixedLevelInclusionOrZero k A (p - 1) 1 m := by
  unfold mixedLevelInclusion
  change (_ ≫ _) ≫ ((connesMixedBicomplex k A).D₁ (ComplexShape.down ℕ) n m +
    (connesMixedBicomplex k A).D₂ (ComplexShape.down ℕ) n m) = _
  erw [comp_add, Category.assoc, Category.assoc,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, mixed_d₁]
  let x : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m :=
    if p = 0 then 0 else connesBoundary k A 0 ≫ mixedLevelInclusionOrZero k A (p - 1) 1 m
  let z : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m :=
    (ChainComplex.mixedColumnIso (bComplex k A) p 0 (0 + p) rfl).inv ≫
      (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p (0 + p) m
  have hz : z = 0 := by
    have hbottom : ∀ (q : ℕ) (hq : 0 + p = q),
        (ChainComplex.mixedColumnIso (bComplex k A) p 0 q hq).inv ≫
          (connesMixedBicomplex k A).d₂ (ComplexShape.down ℕ) p q m = 0 := by
      intro q hq
      have hqp : q = p := hq.symm.trans (Nat.zero_add p)
      cases hqp
      exact mixed_d₂_bottom k A p m
    exact hbottom (0 + p) rfl
  change x + z = x
  exact (congrArg (fun a : chainLevel k A A 0 ⟶ (connesMixedTotal k A).X m => x + a) hz).trans
    (add_zero x)

theorem connesOddInclusion_dOrZero (j r n m : ℕ)
    (h : (r + 1) + (2 * j + 1) = n) :
    connesOddInclusion k A j (r + 1) n h ≫ (connesOddTotal k A).d n m =
      -(bPrimeComplex k A).d (r + 1) r ≫ connesOddInclusionOrZero k A j r m := by
  by_cases hm : r + (2 * j + 1) = m
  · erw [connesOddInclusionOrZero_eq k A j r m hm, connesOddInclusion_d]
  · have hnm : ¬ (ComplexShape.down ℕ).Rel n m := by
      change m + 1 ≠ n
      omega
    erw [(connesOddTotal k A).shape n m hnm, comp_zero, connesOddInclusionOrZero,
      dif_neg hm, comp_zero]
    exact neg_zero.symm

theorem connesOddInclusion_d_bottom (j n m : ℕ) (h : 0 + (2 * j + 1) = n) :
    connesOddInclusion k A j 0 n h ≫ (connesOddTotal k A).d n m = 0 := by
  let P := connesOddFamily k A
  let X : ℕ → ModuleCat.{max u v} k := P.X n
  let Y : ℕ → ModuleCat.{max u v} k := P.X m
  let f : ∀ a : ℕ, X a ⟶ Y a := P.d n m
  let a : chainLevel k A A 0 ⟶ X j :=
    (ChainComplex.mixedColumnIso (bPrimeComplex k A) (2 * j + 1) 0 n h).inv
  let i : X j ⟶ (connesOddTotal k A).X n := Sigma.ι X j
  let i' : Y j ⟶ (connesOddTotal k A).X m := Sigma.ι Y j
  let t : (connesOddTotal k A).X n ⟶ (connesOddTotal k A).X m :=
    CategoryTheory.Limits.Sigma.map f
  have hi : i ≫ t = f j ≫ i' := CategoryTheory.Limits.Sigma.ι_map f j
  let K := bPrimeComplex k A
  let E : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
    ComplexShape.embeddingDown'Add (1 : ℕ) (2 * j + 1)
  let L : ChainComplex (ModuleCat.{max u v} k) ℕ := K.extend E
  let d : L.X n ⟶ L.X m := L.d n m
  let σ : ℤˣ := (-1 : ℤˣ) ^ (2 * j + 1)
  have hd : d = 0 := K.extend_d_from_eq_zero E n m 0 h
    (by simp [ComplexShape.down_Rel])
  have hv : f j = σ • d := rfl
  have hf : f j = 0 := hv.trans
    ((congrArg (fun g : L.X n ⟶ L.X m => σ • g) hd).trans (smul_zero σ))
  have ht : i ≫ t = 0 := hi.trans
    ((congrArg (fun g : X j ⟶ Y j => g ≫ i') hf).trans zero_comp)
  have hall : (a ≫ i) ≫ t = 0 := (Category.assoc a i t).trans
    ((congrArg (fun g : X j ⟶ (connesOddTotal k A).X m => a ≫ g) ht).trans comp_zero)
  change (a ≫ i) ≫ t = 0
  exact hall

theorem boundary_comp_levelImage (p r n : ℕ) :
    connesBoundary k A r ≫ mixedToCyclicLevelImage k A p (r + 1) n =
      connesBoundary k A r ≫
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 1) n := by
  let B : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := connesBoundary k A r
  let N : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) := normMap k A (r + 1)
  let S : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := extraDegeneracy k A (r + 1)
  let i₀ : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 1) n
  let i₁ : chainLevel k A A (r + 2) ⟶ (cyclicTotal k A).X n :=
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 2) n
  let c : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
    if p = 0 then 0 else N ≫ S ≫ i₁
  have hImage : mixedToCyclicLevelImage k A p (r + 1) n = i₀ + c := rfl
  have hB : B ≫ N ≫ S = 0 := boundary_comp_norm_extra k A r
  have hz : B ≫ (N ≫ S ≫ i₁) = 0 := by
    calc
      _ = B ≫ ((N ≫ S) ≫ i₁) :=
        congrArg (fun a : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n => B ≫ a)
          (Category.assoc N S i₁).symm
      _ = (B ≫ (N ≫ S)) ≫ i₁ := (Category.assoc B (N ≫ S) i₁).symm
      _ = 0 ≫ i₁ :=
        congrArg (fun a : chainLevel k A A r ⟶ chainLevel k A A (r + 2) => a ≫ i₁) hB
      _ = 0 := zero_comp
  have hc : B ≫ c = 0 := by
    by_cases hp : p = 0
    · dsimp only [c]
      rw [if_pos hp, comp_zero]
    · dsimp only [c]
      rw [if_neg hp]
      exact hz
  change B ≫ mixedToCyclicLevelImage k A p (r + 1) n = B ≫ i₀
  calc
    _ = B ≫ (i₀ + c) :=
      congrArg (fun a : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n => B ≫ a) hImage
    _ = B ≫ i₀ + B ≫ c :=
      Preadditive.comp_add (chainLevel k A A r) (chainLevel k A A (r + 1))
        ((cyclicTotal k A).X n) B i₀ c
    _ = B ≫ i₀ + 0 :=
      congrArg (fun a : chainLevel k A A r ⟶ (cyclicTotal k A).X n => B ≫ i₀ + a) hc
    _ = B ≫ i₀ := add_zero _

theorem oneSub_comp_evenImage (p r n : ℕ) :
    (𝟙 (chainLevel k A A r) - cyclicMap k A r) ≫ cyclicToOddEvenImage k A p r n = 0 := by
  unfold cyclicToOddEvenImage
  by_cases hp : p = 0
  · erw [if_pos hp, comp_zero]
  · erw [if_neg hp, comp_neg]
    have hz := congrArg (fun a => a ≫ extraDegeneracy k A r ≫
      connesOddInclusionOrZero k A (p - 1) (r + 1) n)
      (oneSubCyclicMap_comp_normMap k A r)
    simpa only [Category.assoc, zero_comp, neg_zero] using congrArg Neg.neg hz

theorem mixedToCyclicComponent_cell_comm (p r n : ℕ) (h : 2 * p + r = n + 1) :
    (mixedLevelInclusion k A p r (n + 1) h ≫ mixedToCyclicComponent k A (n + 1)) ≫
        (cyclicTotal k A).d (n + 1) n =
      (mixedLevelInclusion k A p r (n + 1) h ≫ (connesMixedTotal k A).d (n + 1) n) ≫
        mixedToCyclicComponent k A n := by
  erw [mixedToCyclicComponent_levelImage]
  cases p with
  | zero =>
    cases r with
    | zero => omega
    | succ r =>
      erw [mixedToCyclicLevelImage, if_pos rfl, add_zero,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 (r + 1)
          (n + 1) (by change 0 + (r + 1) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even k A 0 (r + 1) n, if_pos rfl,
        cyclic_d₂_even k A 0 r n, zero_add,
        mixedInclusion_d_succ k A 0 r (n + 1) n h, if_pos rfl, zero_add,
        Category.assoc, mixedToCyclicComponent_inclusionOrZero]
      simp only [mixedToCyclicLevelImage, if_pos rfl, if_true, add_zero]
      erw [_root_.add_zero]
  | succ p =>
    have hc : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    cases r with
    | zero =>
      erw [mixedToCyclicLevelImage, if_neg (Nat.succ_ne_zero p), hc, add_comp,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) 0
          (n + 1) (by change 2 * (p + 1) + 0 = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even,
        if_neg (Nat.succ_ne_zero p), cyclic_d₂_bottom, add_zero, hc,
        Category.assoc, Category.assoc,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p + 1) 1
          (n + 1) (by change (2 * p + 1) + 1 = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd,
        mixedInclusion_d_bottom k A (p + 1) (n + 1) n h,
        if_neg (Nat.succ_ne_zero p), Nat.add_sub_cancel]
      conv_rhs => repeat erw [Category.assoc]
      erw [mixedToCyclicComponent_inclusionOrZero k A p 1 n,
        boundary_comp_levelImage k A p 0 n]
      let N : chainLevel k A A 0 ⟶ chainLevel k A A 0 := normMap k A 0
      let S : chainLevel k A A 0 ⟶ chainLevel k A A 1 := extraDegeneracy k A 0
      let d : chainLevel k A A 1 ⟶ chainLevel k A A 0 := (bPrimeComplex k A).d 1 0
      let T : chainLevel k A A 1 ⟶ chainLevel k A A 1 := cyclicMap k A 1
      let B : chainLevel k A A 0 ⟶ chainLevel k A A 1 := connesBoundary k A 0
      let io : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) 0 n
      let ie : chainLevel k A A 1 ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) 1 n
      have hCancel : (N ≫ S) ≫ d = N := norm_extra_contraction_bottom k A
      have hBoundary : (N ≫ S) ≫ (𝟙 (chainLevel k A A 1) - T) = B :=
        (Category.assoc N S _).trans (connesBoundary_eq k A 0).symm
      have ho : (N ≫ S) ≫ (d ≫ io) = N ≫ io :=
        (Category.assoc (N ≫ S) d io).symm.trans
          (congrArg (fun f : chainLevel k A A 0 ⟶ chainLevel k A A 0 => f ≫ io) hCancel)
      have he : (N ≫ S) ≫ ((𝟙 (chainLevel k A A 1) - T) ≫ ie) = B ≫ ie :=
        (Category.assoc (N ≫ S) _ ie).symm.trans
          (congrArg (fun f : chainLevel k A A 0 ⟶ chainLevel k A A 1 => f ≫ ie) hBoundary)
      change N ≫ io + (N ≫ S) ≫
        ((𝟙 (chainLevel k A A 1) - T) ≫ ie + -(d ≫ io)) = B ≫ ie
      calc
        _ = N ≫ io + (N ≫ S) ≫ ((𝟙 (chainLevel k A A 1) - T) ≫ ie) -
            (N ≫ S) ≫ (d ≫ io) := by
          erw [comp_add, comp_neg]
          simp only [sub_eq_add_neg, Preadditive.neg_comp, Category.assoc]
          abel
        _ = N ≫ io + B ≫ ie - N ≫ io :=
          congrArg₂ (fun f g : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n => N ≫ io + f - g) he ho
        _ = B ≫ ie := by abel
    | succ r =>
      erw [mixedToCyclicLevelImage, if_neg (Nat.succ_ne_zero p), hc, add_comp,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) (r + 1)
          (n + 1) (by change 2 * (p + 1) + (r + 1) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_even,
        if_neg (Nat.succ_ne_zero p), cyclic_d₂_even, hc,
        Category.assoc, Category.assoc,
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p + 1) (r + 2)
          (n + 1) (by change (2 * p + 1) + (r + 2) = n + 1; omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd,
        mixedInclusion_d_succ k A (p + 1) r (n + 1) n h,
        if_neg (Nat.succ_ne_zero p), Nat.add_sub_cancel,
        add_comp, Category.assoc, Category.assoc]
      conv_rhs => repeat erw [Category.assoc]
      erw [mixedToCyclicComponent_inclusionOrZero k A p (r + 2) n,
        mixedToCyclicComponent_inclusionOrZero k A (p + 1) r n,
        boundary_comp_levelImage k A p (r + 1) n]
      let N : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) := normMap k A (r + 1)
      let S : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := extraDegeneracy k A (r + 1)
      let d : chainLevel k A A (r + 2) ⟶ chainLevel k A A (r + 1) :=
        (bPrimeComplex k A).d (r + 2) (r + 1)
      let d₀ : chainLevel k A A (r + 1) ⟶ chainLevel k A A r := (bComplex k A).d (r + 1) r
      let N₀ : chainLevel k A A r ⟶ chainLevel k A A r := normMap k A r
      let S₀ : chainLevel k A A r ⟶ chainLevel k A A (r + 1) := extraDegeneracy k A r
      let T : chainLevel k A A (r + 2) ⟶ chainLevel k A A (r + 2) := cyclicMap k A (r + 2)
      let B : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) := connesBoundary k A (r + 1)
      let io : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) (r + 1) n
      let ie : chainLevel k A A (r + 2) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) (r + 2) n
      let i₀ : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * (p + 1)) r n
      have hImage : mixedToCyclicLevelImage k A (p + 1) r n = i₀ + N₀ ≫ S₀ ≫ io := by
        dsimp only [mixedToCyclicLevelImage]
        erw [if_neg (Nat.succ_ne_zero p), hc] <;> rfl
      have hCancel : (N ≫ S) ≫ d + d₀ ≫ N₀ ≫ S₀ = N := norm_extra_contraction_succ k A r
      have hBoundary : (N ≫ S) ≫ (𝟙 (chainLevel k A A (r + 2)) - T) = B :=
        (Category.assoc N S _).trans (connesBoundary_eq k A (r + 1)).symm
      have ho : N ≫ io = ((N ≫ S) ≫ d) ≫ io + (d₀ ≫ N₀ ≫ S₀) ≫ io := by
        have h := congrArg
          (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) => f ≫ io) hCancel
        rw [add_comp] at h
        exact h.symm
      have he : (N ≫ S) ≫ ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie) = B ≫ ie :=
        (Category.assoc (N ≫ S) _ ie).symm.trans
          (congrArg (fun f : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 2) => f ≫ ie) hBoundary)
      erw [hImage]
      change N ≫ io + d₀ ≫ i₀ + (N ≫ S) ≫
        ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie + -(d ≫ io)) =
          B ≫ ie + d₀ ≫ (i₀ + N₀ ≫ S₀ ≫ io)
      calc
        _ = N ≫ io + d₀ ≫ i₀ + (N ≫ S) ≫
            ((𝟙 (chainLevel k A A (r + 2)) - T) ≫ ie) - (N ≫ S) ≫ (d ≫ io) := by
          erw [comp_add, comp_neg]
          simp only [sub_eq_add_neg, Preadditive.neg_comp, Category.assoc]
          abel
        _ = N ≫ io + d₀ ≫ i₀ + B ≫ ie - ((N ≫ S) ≫ d) ≫ io :=
          congrArg₂ (fun f g : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n =>
            N ≫ io + d₀ ≫ i₀ + f - g) he (Category.assoc (N ≫ S) d io).symm
        _ = B ≫ ie + d₀ ≫ i₀ + (d₀ ≫ N₀ ≫ S₀) ≫ io := by
          rw [ho]
          abel
        _ = B ≫ ie + d₀ ≫ (i₀ + N₀ ≫ S₀ ≫ io) := by
          erw [comp_add]
          simp only [Category.assoc]
          abel

theorem mixedToCyclicComponent_comm (n : ℕ) :
    mixedToCyclicComponent k A (n + 1) ≫ (cyclicTotal k A).d (n + 1) n =
      (connesMixedTotal k A).d (n + 1) n ≫ mixedToCyclicComponent k A n := by
  apply connesMixedTotal_hom_ext k A (n + 1)
  intro p r h
  simpa only [Category.assoc] using mixedToCyclicComponent_cell_comm k A p r n h

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The maps `i_n`, with the positive `sN` coordinate
correction, assemble into a chain map `i : T → Z`. -/
def mixedToCyclic : connesMixedTotal k A ⟶ cyclicTotal k A :=
  ChainComplex.ofHom (mixedToCyclicComponent k A) (mixedToCyclicComponent_comm k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The degree-`n` component of the mixed-to-cyclic chain
map is the coordinate-descent map `i_n`. -/
@[simp]
theorem mixedToCyclic_f (n : ℕ) : (mixedToCyclic k A).f n = mixedToCyclicComponent k A n := rfl

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. The mixed first-column inclusion satisfies
`J_(0,r,r) ≫ i_r = I_(0,r,r)`; its correction term is zero. -/
theorem mixedToCyclic_ι_zero (r : ℕ) :
    mixedLevelInclusion k A 0 r r (by omega) ≫ (mixedToCyclic k A).f r =
      (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) 0 r r (by change 0 + r = r; omega) := by
  erw [mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  dsimp only [mixedToCyclicLevelImage]
  erw [if_pos rfl, add_zero]
  exact (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 r r
    (by change 0 + r = r; omega)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Set `C_r=A ⊗[k] A^⊗r`,
`u_r=s_r ∘ N_r` with unit insertion `s_r` and signed cyclic norm `N_r`. Let `Z` be the cyclic total with column injections
`I_(c,r,n)`, `T` the mixed total with injections `J_(p,r,n)` for
`2p+r=n`, and `O` the odd-column total with injections `K_(j,r,n)`
for `r+2j+1=n`. Each injection is zero outside its indicated degree. For `2(p+1)+r=n`, the mixed-to-cyclic map has value
`I_(2p+2,r,n) + u_r ≫ I_(2p+1,r+1,n)` on the mixed
column `(p+1,r)`. -/
theorem mixedToCyclic_ι_succ (p r n : ℕ) (h : 2 * (p + 1) + r = n) :
    mixedLevelInclusion k A (p + 1) r n h ≫ (mixedToCyclic k A).f n =
      (let x : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * (p + 1)) r n h
       let y : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
          normMap k A r ≫ extraDegeneracy k A r ≫
            (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p + 1) (r + 1) n
              (by change (2 * p + 1) + (r + 1) = n; omega)
       x + y) := by
  erw [mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  unfold mixedToCyclicLevelImage
  erw [if_neg (Nat.succ_ne_zero p),
    (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * (p + 1)) r n h]
  have hc : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
  erw [hc, (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ)
    (2 * p + 1) (r + 1) n (by change (2 * p + 1) + (r + 1) = n; omega)]

theorem cyclicToOddComponent_cell_comm (c r n : ℕ) (h : c + r = n + 1) :
    ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r (n + 1) h ≫
        cyclicToOddComponent k A (n + 1)) ≫ (connesOddTotal k A).d (n + 1) n =
      ((cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) c r (n + 1) h ≫
        (cyclicTotal k A).d (n + 1) n) ≫ cyclicToOddComponent k A n := by
  by_cases hc : Even c
  · obtain ⟨p, hp⟩ := hc
    have hcp : c = 2 * p := by omega
    clear hp
    subst c
    cases p with
    | zero =>
      cases r with
      | zero => omega
      | succ r =>
        have hZero : connesOddInclusionOrZero k A (0 - 1) (r + 2) (n + 1) = 0 := by
          unfold connesOddInclusionOrZero
          exact dif_neg (by omega)
        erw [cyclicToOddComponent_even k A 0 (r + 1) (n + 1) h,
          hZero, comp_zero, neg_zero, zero_comp]
        erw [cyclicInclusion_d, cyclic_d₁_even, if_pos rfl, cyclic_d₂_even, zero_add,
          Category.assoc, cyclicToOddComponent_evenOrZero]
        simp only [cyclicToOddEvenImage, if_pos rfl, if_true, comp_zero]
        erw [comp_zero]
    | succ p =>
      have hcol : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
      erw [cyclicToOddComponent_even]
      cases r with
      | zero =>
        erw [connesOddInclusionOrZero_eq k A p 1 (n + 1) (by omega), neg_comp,
          Category.assoc, Category.assoc, connesOddInclusion_dOrZero,
          cyclicInclusion_d, cyclic_d₁_even, if_neg (Nat.succ_ne_zero p),
          cyclic_d₂_bottom, add_zero, hcol]
        let N : chainLevel k A A 0 ⟶ chainLevel k A A 0 := normMap k A 0
        let s : chainLevel k A A 0 ⟶ chainLevel k A A 1 := extraDegeneracy k A 0
        let d : chainLevel k A A 1 ⟶ chainLevel k A A 0 := (bPrimeComplex k A).d 1 0
        let io : chainLevel k A A 0 ⟶ (cyclicTotal k A).X n :=
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p + 1) 0 n
        let iq : chainLevel k A A 0 ⟶ (connesOddTotal k A).X n :=
          connesOddInclusionOrZero k A p 0 n
        let q : (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
          cyclicToOddComponent k A n
        have ho : io ≫ q = iq := cyclicToOddComponent_oddOrZero k A p 0 n
        have hCancel : ((N ≫ s) ≫ d) ≫ iq = N ≫ iq :=
          congrArg (fun a : chainLevel k A A 0 ⟶ chainLevel k A A 0 => a ≫ iq)
            (norm_extra_contraction_bottom k A)
        change @Eq (chainLevel k A A 0 ⟶ (connesOddTotal k A).X n)
          (-(N ≫ s ≫ (-(d ≫ iq)))) ((N ≫ io) ≫ q)
        erw [Category.assoc N io q, ho]
        simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
        simpa only [Category.assoc] using hCancel
      | succ r =>
        erw [connesOddInclusionOrZero_eq k A p (r + 2) (n + 1) (by omega), neg_comp,
          Category.assoc, Category.assoc, connesOddInclusion_dOrZero,
          cyclicInclusion_d, cyclic_d₁_even, if_neg (Nat.succ_ne_zero p),
          cyclic_d₂_even, hcol,
          add_comp, Category.assoc, Category.assoc,
          cyclicToOddComponent_oddOrZero, cyclicToOddComponent_evenOrZero]
        let X₀ := chainLevel k A A r
        let X₁ := chainLevel k A A (r + 1)
        let X₂ := chainLevel k A A (r + 2)
        let N₀ : X₀ ⟶ X₀ := normMap k A r
        let N₁ : X₁ ⟶ X₁ := normMap k A (r + 1)
        let s₀ : X₀ ⟶ X₁ := extraDegeneracy k A r
        let s₁ : X₁ ⟶ X₂ := extraDegeneracy k A (r + 1)
        let d₀ : X₁ ⟶ X₀ := (bComplex k A).d (r + 1) r
        let d₁' : X₂ ⟶ X₁ := (bPrimeComplex k A).d (r + 2) (r + 1)
        let iq : X₁ ⟶ (connesOddTotal k A).X n :=
          connesOddInclusionOrZero k A p (r + 1) n
        change @Eq (X₁ ⟶ (connesOddTotal k A).X n)
          (-(N₁ ≫ s₁ ≫ (-(d₁' ≫ iq))))
          (N₁ ≫ iq + d₀ ≫ (-(N₀ ≫ s₀ ≫ iq)))
        have hContraction : (N₁ ≫ s₁) ≫ d₁' + d₀ ≫ N₀ ≫ s₀ = N₁ :=
          norm_extra_contraction_succ k A r
        have hCancel := congrArg (fun x : X₁ ⟶ X₁ => x ≫ iq) hContraction
        rw [Preadditive.add_comp] at hCancel
        simp only [Category.assoc] at hCancel
        simp only [neg_one_zsmul, Units.neg_smul, one_smul,
          Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, Category.assoc]
        erw [← hCancel]
        abel
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hc
    have hcj : c = 2 * j + 1 := by omega
    clear hj
    subst c
    erw [cyclicToOddComponent_odd]
    cases r with
    | zero =>
      erw [connesOddInclusion_d_bottom k A j (n + 1) n (by omega),
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_bottom, add_zero,
        Category.assoc, cyclicToOddComponent_evenOrZero, oneSub_comp_evenImage]
    | succ r =>
      erw [connesOddInclusion_dOrZero,
        cyclicInclusion_d, cyclic_d₁_odd, cyclic_d₂_odd, add_comp]
      let d : chainLevel k A A (r + 1) ⟶ chainLevel k A A r :=
        (bPrimeComplex k A).d (r + 1) r
      let a : chainLevel k A A (r + 1) ⟶ chainLevel k A A (r + 1) :=
        𝟙 (chainLevel k A A (r + 1)) - cyclicMap k A (r + 1)
      let ie : chainLevel k A A (r + 1) ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j) (r + 1) n
      let io : chainLevel k A A r ⟶ (cyclicTotal k A).X n :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n
      let iq : chainLevel k A A r ⟶ (connesOddTotal k A).X n :=
        connesOddInclusionOrZero k A j r n
      let q : (cyclicTotal k A).X n ⟶ (connesOddTotal k A).X n :=
        cyclicToOddComponent k A n
      have hEven : ie ≫ q = cyclicToOddEvenImage k A j (r + 1) n :=
        cyclicToOddComponent_evenOrZero k A j (r + 1) n
      have hOdd : io ≫ q = iq := cyclicToOddComponent_oddOrZero k A j r n
      have he : (a ≫ ie) ≫ q = 0 :=
        (Category.assoc a ie q).trans
          ((congrArg (fun x : chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n =>
            a ≫ x) hEven).trans (oneSub_comp_evenImage k A j (r + 1) n))
      have ho : (-(d ≫ io)) ≫ q = -(d ≫ iq) := by
        rw [Preadditive.neg_comp, Category.assoc d io q, hOdd]
      change @Eq (chainLevel k A A (r + 1) ⟶ (connesOddTotal k A).X n)
        (-(d ≫ iq)) (((a ≫ ie) ≫ q) + ((-(d ≫ io)) ≫ q))
      exact ((congrArg₂ (fun x y : chainLevel k A A (r + 1) ⟶
          (connesOddTotal k A).X n => x + y) he ho).trans (zero_add (-(d ≫ iq)))).symm

theorem cyclicToOddComponent_comm (n : ℕ) :
    cyclicToOddComponent k A (n + 1) ≫ (connesOddTotal k A).d (n + 1) n =
      (cyclicTotal k A).d (n + 1) n ≫ cyclicToOddComponent k A n := by
  apply HomologicalComplex₂.total.hom_ext
  intro c r h
  simpa only [Category.assoc] using cyclicToOddComponent_cell_comm k A c r n h

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The degreewise odd projection is a chain map
`π : Z → O`. -/
def cyclicToOdd : cyclicTotal k A ⟶ connesOddTotal k A :=
  ChainComplex.ofHom (cyclicToOddComponent k A) (cyclicToOddComponent_comm k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The degree-`n` component of `π` is the computed
projection using `-sN` on even columns and identity on odd columns. -/
@[simp]
theorem cyclicToOdd_f (n : ℕ) : (cyclicToOdd k A).f n = cyclicToOddComponent k A n := rfl

theorem mixedEvenProjection_evenOrZero (p r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n ≫
        mixedEvenProjection k A n = mixedLevelInclusionOrZero k A p r n := by
  by_cases h : 2 * p + r = n
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p) r n h,
      mixedEvenProjection_even k A p r n h, mixedLevelInclusionOrZero_eq k A p r n h]
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ) (2 * p) r n h,
      zero_comp]
    unfold mixedLevelInclusionOrZero
    erw [(connesMixedBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p (r + p) n
      (by change p + (r + p) ≠ n; omega), comp_zero] <;> rfl

theorem mixedEvenProjection_oddOrZero (j r n : ℕ) :
    (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * j + 1) r n ≫
        mixedEvenProjection k A n = 0 := by
  by_cases h : 2 * j + 1 + r = n
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * j + 1) r n h,
      mixedEvenProjection_odd k A j r n h]
  · erw [(cyclicBicomplex k A).ιTotalOrZero_eq_zero (ComplexShape.down ℕ)
      (2 * j + 1) r n h, zero_comp]

theorem mixedToCyclic_evenProjection (n : ℕ) :
    (mixedToCyclic k A).f n ≫ mixedEvenProjection k A n = 𝟙 _ := by
  apply connesMixedTotal_hom_ext k A n
  intro p r h
  erw [← Category.assoc, mixedToCyclic_f, mixedToCyclicComponent_levelImage]
  unfold mixedToCyclicLevelImage
  erw [add_comp, mixedEvenProjection_evenOrZero, mixedLevelInclusionOrZero_eq k A p r n h]
  by_cases hp : p = 0
  · erw [if_pos hp, zero_comp, add_zero, Category.comp_id]
  · let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let C := (cyclicTotal k A).X n
    let M := (connesMixedTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    let i : Y ⟶ C :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    let P : C ⟶ M := mixedEvenProjection k A n
    let x : X ⟶ M := mixedLevelInclusion k A p r n h
    have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
    have hi : i ≫ P = 0 := by
      change (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n ≫ mixedEvenProjection k A n = 0
      erw [hcol]
      exact mixedEvenProjection_oddOrZero k A (p - 1) (r + 1) n
    have hy : (N ≫ S ≫ i) ≫ P = 0 := by
      calc
        _ = (N ≫ S) ≫ (i ≫ P) := by simp only [Category.assoc]
        _ = (N ≫ S) ≫ (0 : Y ⟶ M) :=
          congrArg (fun f : Y ⟶ M => (N ≫ S) ≫ f) hi
        _ = 0 := comp_zero
    erw [if_neg hp]
    change x + (N ≫ S ≫ i) ≫ P = x
    exact (congrArg (fun f : X ⟶ M => x + f) hy).trans (add_zero x)
theorem oddSection_cyclicToOdd (n : ℕ) :
    connesOddSection k A n ≫ (cyclicToOdd k A).f n = 𝟙 _ := by
  apply connesOddTotal_hom_ext k A n
  intro j r h
  erw [← Category.assoc, connesOddInclusion_section, cyclicToOdd_f,
    cyclicToOddComponent_oddOrZero, connesOddInclusionOrZero_eq k A j r n h,
    Category.comp_id]

theorem mixedToCyclic_comp_cyclicToOdd : mixedToCyclic k A ≫ cyclicToOdd k A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (mixedToCyclic k A).f n ≫ (cyclicToOdd k A).f n = 0
  apply connesMixedTotal_hom_ext k A n
  intro p r h
  erw [← Category.assoc, mixedToCyclic_f, mixedToCyclicComponent_levelImage, cyclicToOdd_f]
  unfold mixedToCyclicLevelImage
  erw [add_comp, cyclicToOddComponent_evenOrZero]
  by_cases hp : p = 0
  · simp only [if_pos hp, cyclicToOddEvenImage, zero_comp, add_zero, comp_zero]
  · let X := chainLevel k A A r
    let Y := chainLevel k A A (r + 1)
    let C := (cyclicTotal k A).X n
    let O := (connesOddTotal k A).X n
    let N : X ⟶ X := normMap k A r
    let S : X ⟶ Y := extraDegeneracy k A r
    let i : Y ⟶ C :=
      (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    let j : Y ⟶ O := connesOddInclusionOrZero k A (p - 1) (r + 1) n
    let Q : C ⟶ O := cyclicToOddComponent k A n
    let F : X ⟶ O := N ≫ S ≫ j
    have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
    have hi : i ≫ Q = j := by
      change (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ)
        (2 * p - 1) (r + 1) n ≫ cyclicToOddComponent k A n = j
      erw [hcol]
      exact cyclicToOddComponent_oddOrZero k A (p - 1) (r + 1) n
    have hy : (N ≫ S ≫ i) ≫ Q = F := by
      calc
        _ = (N ≫ S) ≫ (i ≫ Q) := by simp only [Category.assoc]
        _ = (N ≫ S) ≫ j := congrArg (fun f : Y ⟶ O => (N ≫ S) ≫ f) hi
        _ = F := Category.assoc N S j
    have hEven : cyclicToOddEvenImage k A p r n = -F := if_neg hp
    erw [if_neg hp]
    change cyclicToOddEvenImage k A p r n + (N ≫ S ≫ i) ≫ Q = 0
    exact (congrArg₂ (fun f g : X ⟶ O => f + g) hEven hy).trans (neg_add_cancel F)
theorem mixedCyclicSplitting_id (n : ℕ) :
    mixedEvenProjection k A n ≫ (mixedToCyclic k A).f n +
        (cyclicToOdd k A).f n ≫ connesOddSection k A n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro c r h
  change c + r = n at h
  erw [comp_add, ← Category.assoc, ← Category.assoc, cyclicToOdd_f]
  by_cases hc : Even c
  · obtain ⟨p, hp⟩ := hc
    have hcp : c = 2 * p := by omega
    clear hp
    subst c
    erw [mixedEvenProjection_even, mixedToCyclic_f, mixedToCyclicComponent_levelImage,
      cyclicToOddComponent_even]
    unfold mixedToCyclicLevelImage
    by_cases hp : p = 0
    · subst p
      have hz : connesOddInclusionOrZero k A (0 - 1) (r + 1) n = 0 := by
        unfold connesOddInclusionOrZero
        erw [dif_neg (by omega)]
      erw [if_pos rfl, hz, comp_zero, neg_zero, zero_comp, add_zero, add_zero]
      simpa only [Category.comp_id] using
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) 0 r n h
    · let X := chainLevel k A A r
      let Y := chainLevel k A A (r + 1)
      let C := (cyclicTotal k A).X n
      let O := (connesOddTotal k A).X n
      let N : X ⟶ X := normMap k A r
      let S : X ⟶ Y := extraDegeneracy k A r
      let i₀ : X ⟶ C :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
      let i : Y ⟶ C :=
        (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
      let j : Y ⟶ O := connesOddInclusionOrZero k A (p - 1) (r + 1) n
      let Q : O ⟶ C := connesOddSection k A n
      let F : X ⟶ O := N ≫ S ≫ j
      let V : X ⟶ C := N ≫ S ≫ i
      have hcol : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
      have hj : j ≫ Q = i := by
        change connesOddInclusionOrZero k A (p - 1) (r + 1) n ≫ connesOddSection k A n =
          (cyclicBicomplex k A).ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
        erw [hcol]
        exact connesOddInclusionOrZero_section k A (p - 1) (r + 1) n
      have hF : F ≫ Q = V := by
        calc
          _ = (N ≫ S) ≫ (j ≫ Q) := by simp only [F, Category.assoc]
          _ = (N ≫ S) ≫ i := congrArg (fun f : Y ⟶ C => (N ≫ S) ≫ f) hj
          _ = V := Category.assoc N S i
      have hNeg : (-F) ≫ Q = -V :=
        (Preadditive.neg_comp F Q).trans (congrArg (fun f : X ⟶ C => -f) hF)
      have hi₀ : i₀ = (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h :=
        (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * p) r n h
      erw [if_neg hp]
      change (i₀ + V) + (-F) ≫ Q =
        (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫ 𝟙 C
      have hAdd : (i₀ + V) + -V = i₀ := _root_.add_neg_cancel_right i₀ V
      have hId : (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h ≫ 𝟙 C =
          (cyclicBicomplex k A).ιTotal (ComplexShape.down ℕ) (2 * p) r n h :=
        Category.comp_id _
      exact (congrArg (fun f : X ⟶ C => (i₀ + V) + f) hNeg).trans
        (hAdd.trans (hi₀.trans hId.symm))
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hc
    have hcj : c = 2 * j + 1 := by omega
    clear hj
    subst c
    erw [mixedEvenProjection_odd, zero_comp, cyclicToOddComponent_odd,
      connesOddInclusion_section, zero_add,
      (cyclicBicomplex k A).ιTotalOrZero_eq (ComplexShape.down ℕ) (2 * j + 1) r n h,
      Category.comp_id]

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The maps `i,π`, with zero composite, define the short
complex `T → Z → O` of nonnegative chain complexes. -/
def mixedCyclicShortComplex : ShortComplex (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  ShortComplex.mk (mixedToCyclic k A) (cyclicToOdd k A)
    (mixedToCyclic_comp_cyclicToOdd k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. Each degree row `T_n → Z_n → O_n` is split by the
 even-coordinate retraction and the odd-coordinate section. -/
def mixedCyclicSplitting (n : ℕ) :
    ((mixedCyclicShortComplex k A).map
      (HomologicalComplex.eval _ (ComplexShape.down ℕ) n)).Splitting where
  r := mixedEvenProjection k A n
  s := connesOddSection k A n
  f_r := mixedToCyclic_evenProjection k A n
  s_g := oddSection_cyclicToOdd k A n
  id := mixedCyclicSplitting_id k A n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The degreewise-split short complex and contraction of
`O` give a chain-homotopy equivalence `T ≃ Z`. -/
def mixedToCyclicHomotopyEquiv : HomotopyEquiv (connesMixedTotal k A) (cyclicTotal k A) :=
  ChainComplex.homotopyEquivOfDegreewiseSplit (mixedCyclicShortComplex k A)
    (mixedCyclicSplitting k A) (connesOddContraction k A)

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The forward map of this homotopy equivalence is
`i : T → Z`. -/
@[simp]
theorem mixedToCyclicHomotopyEquiv_hom :
    (mixedToCyclicHomotopyEquiv k A).hom = mixedToCyclic k A :=
  ChainComplex.homotopyEquivOfDegreewiseSplit_hom _ _ _

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The mixed-to-cyclic chain map `i` is a quasi-isomorphism. -/
theorem mixedToCyclic_quasiIso : QuasiIso (mixedToCyclic k A) := by
  simpa only [mixedToCyclicHomotopyEquiv_hom] using
    (mixedToCyclicHomotopyEquiv k A).quasiIso_hom

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. Taking homology gives a canonical comparison
`H_n(T) ≅ HC_n(k,A)=H_n(Z)`. -/
def mixedCyclicHomologyIso (n : ℕ) :
    (connesMixedTotal k A).homology n ≅ cyclicHomology k A n :=
  (mixedToCyclicHomotopyEquiv k A).toHomologyIso n

/-- Let `k` be a commutative ring and `A` a unital ring with
compatible central `k`-action. Let `T` be its Connes mixed total,
`Z` its cyclic total, and `O` the contractible translated odd-column
sum. The mixed-to-cyclic map `i : T → Z` uses the positive `sN`
correction, and the odd projection uses `(-sN,id)` on even/odd coordinates. The forward map of `H_n(T) ≅ HC_n(k,A)` is
`H_n(i)`. -/
@[simp]
theorem mixedCyclicHomologyIso_hom (n : ℕ) :
    (mixedCyclicHomologyIso k A n).hom = homologyMap (mixedToCyclic k A) n := by
  change homologyMap (mixedToCyclicHomotopyEquiv k A).hom n = _
  rw [mixedToCyclicHomotopyEquiv_hom]

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The lifted mixed total is canonically isomorphic to
the total of the lifted mixed bicomplex:
`L_ℓ(Tot K_mix) ≅ Tot(L_ℓ K_mix)`. -/
def connesMixedTotalLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedTotal k A) ≅
        ((HomologicalComplex₂.total
            ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
            (connesMixedBicomplex k A))) (ComplexShape.down ℕ)) := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let R := connesMixedBicomplex k A
  letI : ∀ n, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) n)) U := fun n => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {n}) :=
      Fintype.ofFinset (Finset.antidiagonal n) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  exact HomologicalComplex₂.functorTotalIso U R

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. Exact lifting and totalization give
`L_ℓ(H_n(Tot K_mix)) ≅ H_n(Tot(L_ℓ K_mix))`. -/
def connesMixedHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj ((connesMixedTotal k A).homology n) ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).homology n := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let h : ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k A)).homology n ≅ U.obj ((connesMixedTotal k A).homology n) :=
    ((connesMixedTotal k A).sc n).mapHomologyIso U
  exact h.symm ≪≫ HomologicalComplex.homologyMapIso (connesMixedTotalLiftIso.{lift} k A) n

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. For `2p+r=n`, the lifted regular term `L_ℓ(C_r(A))`
has its supported summand injection into
`Tot(L_ℓ K_mix)_n`. -/
def mixedLevelInclusionLift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (p r n : ℕ) (h : 2 * p + r = n) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).obj (chainLevel k A A r) ⟶
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).X n :=
  (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map
      (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv ≫
    (HomologicalComplex₂.ιTotal
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. Lifting a supported mixed-level injection and then
the total-lift comparison gives the supported injection into
the total of the lifted mixed bicomplex. -/
@[reassoc]
theorem map_mixedLevelInclusion_lift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (p r n : ℕ) (h : 2 * p + r = n) :
    (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map (mixedLevelInclusion k A p r n h) ≫
        (connesMixedTotalLiftIso.{lift} k A).hom.f n =
      mixedLevelInclusionLift.{lift} k A p r n h := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let R := connesMixedBicomplex k A
  letI : ∀ m, PreservesColimit (Discrete.functor
      (R.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) U := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  let a := (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl).inv
  let i := R.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj R
  have hι : U.map i ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom =
      P.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega) :=
    HomologicalComplex₂.map_ιTotal_functorTotalIsoComponent_hom U R p (r + p) n (by change p + (r + p) = n; omega)
  change U.map (a ≫ i) ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom =
    U.map a ≫ P.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  exact (congrArg (fun f => f ≫ (HomologicalComplex₂.functorTotalIsoComponent U R n).hom)
    (U.map_comp a i)).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => U.map a ≫ f) hι))

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. Transporting the lifted positive mixed-to-cyclic
chain map through the two total-lift comparisons gives
`i^ℓ : Tot(L_ℓ K_mix) → Tot(L_ℓ K_cyc)`. -/
def mixedToCyclicLift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)) ⟶
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ)) :=
  (connesMixedTotalLiftIso.{lift} k A).inv ≫
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (mixedToCyclic k A) ≫
        (cyclicTotalLiftIso.{lift} k A).hom

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The lifted comparison satisfies
`L_ℓ(i) ≫ E_cyc = E_mix ≫ i^ℓ`, where `E` denotes the
total-lift isomorphism. -/
@[reassoc]
theorem map_mixedToCyclic_lift.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (mixedToCyclic k A) ≫
          (cyclicTotalLiftIso.{lift} k A).hom =
      (connesMixedTotalLiftIso.{lift} k A).hom ≫ mixedToCyclicLift.{lift} k A := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let eM := connesMixedTotalLiftIso.{lift} k A
  let eC := cyclicTotalLiftIso.{lift} k A
  let i := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map (mixedToCyclic k A)
  change i ≫ eC.hom = eM.hom ≫ (eM.inv ≫ i ≫ eC.hom)
  exact (eM.hom_inv_id_assoc (i ≫ eC.hom)).symm

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The transported map `i^ℓ` is a quasi-isomorphism,
by exact carrier lifting of `i` and the two total comparisons. -/
instance mixedToCyclicLift_quasiIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    _root_.QuasiIso (mixedToCyclicLift.{lift} k A) := by
  letI : _root_.QuasiIso (mixedToCyclic k A) := mixedToCyclic_quasiIso k A
  unfold mixedToCyclicLift
  infer_instance

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The lifted chain comparison induces
`H_n(Tot(L_ℓ K_mix)) ≅ H_n(Tot(L_ℓ K_cyc))`. -/
def mixedCyclicHomologyLiftIso.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).homology n ≅
      ((HomologicalComplex₂.total
          ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (cyclicBicomplex k A))) (ComplexShape.down ℕ)).homology n :=
  asIso (HomologicalComplex.homologyMap (mixedToCyclicLift.{lift} k A) n)

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The forward lifted homology comparison is
`H_n(i^ℓ)`. -/
theorem mixedCyclicHomologyLiftIso_hom.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (mixedCyclicHomologyLiftIso.{lift} k A n).hom =
      HomologicalComplex.homologyMap (mixedToCyclicLift.{lift} k A) n := rfl

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. Morphisms from degree `n` of the lifted mixed total
to any module at the common height are equal if they agree
after all supported injections `2p+r=n`. -/
theorem connesMixedTotalLift_hom_ext.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    {X : ModuleCat.{max lift ground algebra} k} (n : ℕ)
    {f g : ((HomologicalComplex₂.total
        ((((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (connesMixedBicomplex k A))) (ComplexShape.down ℕ)).X n ⟶ X}
    (h : ∀ p r (hr : 2 * p + r = n),
      mixedLevelInclusionLift.{lift} k A p r n hr ≫ f =
        mixedLevelInclusionLift.{lift} k A p r n hr ≫ g) : f = g := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)
  apply HomologicalComplex₂.total.hom_ext
  intro p q hn
  by_cases hpq : p ≤ q
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, q = r + p :=
      ⟨q - p, (Nat.sub_add_cancel hpq).symm⟩
    have hr : 2 * p + r = n := by
      change p + (r + p) = n at hn
      omega
    let e₀ := ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl
    let e : (P.X p).X (r + p) ≅ U.obj ((bComplex k A).X r) := U.mapIso e₀
    let ι : (P.X p).X (r + p) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotal (ComplexShape.down ℕ) p (r + p) n hn
    have he : e.inv = U.map e₀.inv := Functor.mapIso_inv U e₀
    apply (cancel_epi e.inv).1
    have hValue := h p r hr
    change (U.map e₀.inv ≫ ι) ≫ f = (U.map e₀.inv ≫ ι) ≫ g at hValue
    change e.inv ≫ ι ≫ f = e.inv ≫ ι ≫ g
    rw [he]
    exact (Category.assoc (U.map e₀.inv) ι f).symm.trans
      (hValue.trans (Category.assoc (U.map e₀.inv) ι g))
  · have hZero : IsZero ((P.X p).X q) :=
      Functor.map_isZero U
        (ChainComplex.mixedBicomplex_isZero_cell (bComplex k A) (connesBoundaryHomotopy k A)
          (fun j => by simpa only [connesBoundaryHomotopy_hom] using
            connesBoundary_square k A j) p q (by omega))
    exact hZero.eq_of_src _ _

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. On supported coordinate `(p,r)` with `2p+r=n`, `i^ℓ`
has the lifted even cyclic injection plus the positive lifted
`s_rN_r` correction in the preceding odd column; at `p=0`
only the even coordinate remains. -/
theorem mixedToCyclicLift_inclusion.{lift, ground, algebra}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A]
    (p r n : ℕ) (h : 2 * p + r = n) :
    let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
    let P : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
    let even : U.obj (chainLevel k A A r) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
    let odd : U.obj (chainLevel k A A (r + 1)) ⟶ (P.total (ComplexShape.down ℕ)).X n :=
      P.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
    mixedLevelInclusionLift.{lift} k A p r n h ≫ (mixedToCyclicLift.{lift} k A).f n =
      even + U.map (normMap k A r) ≫ U.map (extraDegeneracy k A r) ≫ odd := by
  let U := ModuleCat.uliftFunctor.{lift, max ground algebra} k
  let RM := connesMixedBicomplex k A
  let RC := cyclicBicomplex k A
  let PM : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RM
  let PC : HomologicalComplex₂ (ModuleCat.{max lift ground algebra} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((U.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RC
  let eM := connesMixedTotalLiftIso.{lift} k A
  let eC := cyclicTotalLiftIso.{lift} k A
  let M := (HomologicalComplex.eval _ (ComplexShape.down ℕ) n).mapIso eM
  let C := (HomologicalComplex.eval _ (ComplexShape.down ℕ) n).mapIso eC
  let v := mixedLevelInclusion k A p r n h
  let i := (mixedToCyclic k A).f n
  let even : chainLevel k A A r ⟶ (RC.total (ComplexShape.down ℕ)).X n :=
    RC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let odd : chainLevel k A A (r + 1) ⟶ (RC.total (ComplexShape.down ℕ)).X n :=
    RC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let evenL : U.obj (chainLevel k A A r) ⟶ (PC.total (ComplexShape.down ℕ)).X n :=
    PC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddL : U.obj (chainLevel k A A (r + 1)) ⟶ (PC.total (ComplexShape.down ℕ)).X n :=
    PC.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let N := normMap k A r
  let s := extraDegeneracy k A r
  have hI : v ≫ i = even + N ≫ s ≫ odd := by
    have hImage : v ≫ mixedToCyclicComponent k A n = even + N ≫ s ≫ odd :=
      mixedToCyclicComponent_inclusion k A p r n h
    have hi : i = mixedToCyclicComponent k A n := mixedToCyclic_f k A n
    exact (congrArg (fun a : (connesMixedTotal k A).X n ⟶ (cyclicTotal k A).X n =>
      v ≫ a) hi).trans hImage
  have hv : U.map v ≫ M.hom = mixedLevelInclusionLift.{lift} k A p r n h :=
    map_mixedLevelInclusion_lift k A p r n h
  have hField : (mixedToCyclicLift.{lift} k A).f n = M.inv ≫ U.map i ≫ C.hom := rfl
  have he : U.map even ≫ C.hom = evenL :=
    map_cyclicInclusionOrZero_lift k A (2 * p) r n
  have ho : U.map odd ≫ C.hom = oddL :=
    map_cyclicInclusionOrZero_lift k A (2 * p - 1) (r + 1) n
  change mixedLevelInclusionLift.{lift} k A p r n h ≫ (mixedToCyclicLift.{lift} k A).f n =
    evenL + U.map N ≫ U.map s ≫ oddL
  calc
    _ = (U.map v ≫ M.hom) ≫ (M.inv ≫ U.map i ≫ C.hom) :=
      congrArg₂ (fun a b => a ≫ b) hv.symm hField
    _ = U.map (v ≫ i) ≫ C.hom := by
      rw [U.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = U.map (even + N ≫ s ≫ odd) ≫ C.hom :=
      congrArg (fun f => U.map f ≫ C.hom) hI
    _ = (U.map even ≫ C.hom) + U.map N ≫ U.map s ≫ (U.map odd ≫ C.hom) := by
      rw [U.map_add, U.map_comp, U.map_comp]
      simp only [Preadditive.add_comp, Category.assoc]
    _ = _ := congrArg₂ (fun a b => a + b) he
      (congrArg (fun f => U.map N ≫ U.map s ≫ f) ho)

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The degree-`n` to `n+1` and `n+1` to `n+2`
components of the lifted Connes homotopy have zero composite. -/
theorem connesBoundaryHomotopyLift_square.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (connesBoundaryHomotopyLift.{ground, algebra, lift} k A).hom n (n + 1) ≫
      (connesBoundaryHomotopyLift.{ground, algebra, lift} k A).hom (n + 1) (n + 2) = 0 := by
  rw [connesBoundaryHomotopyLift_hom, connesBoundaryHomotopyLift_hom,
    ← Functor.map_comp, connesBoundary_square, Functor.map_zero]

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The lifted regular `b`-complex and lifted Connes
components form a mixed complex at height `max(u,v,ℓ)`. -/
def connesMixedComplexModelLift.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] : MixedComplex (ModuleCat.{max ground algebra lift} k) :=
  MixedComplex.ofBoundaryHomotopy
    (((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (bComplex k A))
    (connesBoundaryHomotopyLift.{ground, algebra, lift} k A)
    (connesBoundaryHomotopyLift_square.{ground, algebra, lift} k A)

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. The underlying chain complex of the lifted mixed
object is `L_ℓ(bComplex(k,A))`. -/
@[simp]
theorem connesMixedComplexModelLift_underlying.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] :
    (connesMixedComplexModelLift.{ground, algebra, lift} k A).underlying =
      ((ModuleCat.uliftFunctor.{lift, max ground algebra} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (bComplex k A) := rfl

/-- Let `k` be a commutative ring in height `u`, `A` a unital
ring in `v` with compatible central `k`-action, and `ℓ` an extra
carrier height. Write `L_ℓ` for carrier lifting to `max(u,v,ℓ)`;
`K_mix,K_cyc` are its mixed and cyclic bicomplexes. Its degree-`n` mixed operator is `L_ℓ(B_n)`. -/
@[simp]
theorem connesMixedComplexModelLift_B.{ground, algebra, lift}
    (k : Type ground) [CommRing k] (A : Type algebra) [Ring A] [Module k A]
    [IsScalarTower k A A] [SMulCommClass k A A] (n : ℕ) :
    (connesMixedComplexModelLift.{ground, algebra, lift} k A).B n =
      (ModuleCat.uliftFunctor.{lift, max ground algebra} k).map (connesBoundary k A n) :=
  connesBoundaryHomotopyLift_hom k A n

section MixedNaturality

variable {k A} {B : Type w} [Ring B] [Module k B]
  [IsScalarTower k B B] [SMulCommClass k B B]

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. The full Hochschild chain map with its Connes
compatibility is a morphism between the lifted mixed complexes. -/
def connesMixedComplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    connesMixedComplexModelLift.{u, v, w} k A ⟶ connesMixedComplexModelLift.{u, w, v} k B :=
  MixedComplex.ofBoundaryHomotopyMap (connesBoundaryHomotopyLift.{u, v, w} k A)
    (connesBoundaryHomotopyLift_square.{u, v, w} k A)
    (connesBoundaryHomotopyLift.{u, w, v} k B)
    (connesBoundaryHomotopyLift_square.{u, w, v} k B)
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne)

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. The underlying chain map of the lifted mixed morphism
is the full boundary map `bComplexMapLift(f)`. -/
@[simp]
theorem connesMixedComplexMapLift_underlying (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (connesMixedComplexMapLift f hOne).underlying = bComplexMapLift f := rfl

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. The mixed-complex morphism induces a map between
the lifted mixed bicomplexes by their translated-column coordinates. -/
def connesMixedBicomplexMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    (((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k A) ⟶
      (((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (connesMixedBicomplex k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := bComplex k A
  let L := bComplex k B
  let H₀A := connesBoundaryHomotopy k A
  let H₀B := connesBoundaryHomotopy k B
  let HA := connesBoundaryHomotopyLift.{u, v, w} k A
  let HB := connesBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ n, H₀A.hom n (n + 1) ≫ H₀A.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀A]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A n
  let hB : ∀ n, H₀B.hom n (n + 1) ≫ H₀B.hom (n + 1) (n + 2) = 0 := fun n => by
    dsimp only [H₀B]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k B n
  let hcA : ∀ n, HA.hom n (n + 1) = UA.map (H₀A.hom n (n + 1)) := fun n =>
    (connesBoundaryHomotopyLift_hom k A n).trans
      (congrArg (fun a => UA.map a) (connesBoundaryHomotopy_hom k A n).symm)
  let hcB : ∀ n, HB.hom n (n + 1) = UB.map (H₀B.hom n (n + 1)) := fun n =>
    (connesBoundaryHomotopyLift_hom k B n).trans
      (congrArg (fun a => UB.map a) (connesBoundaryHomotopy_hom k B n).symm)
  exact ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (connesMixedComplexMapLift f hOne).underlying
    (fun n => (connesMixedComplexMapLift f hOne).comm_B n)

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. For a supported cell with `n+p=q`, the bicomplex-map
component, under the lifted cell identifications, is `Φ_n`
on the regular Hochschild degree `n`. -/
theorem connesMixedBicomplexMapLift_component (f : A →ₙₐ[k] B) (hOne : f 1 = 1)
    (p n q : ℕ) (h : n + p = q) :
    ((connesMixedBicomplexMapLift f hOne).f p).f q =
      (ModuleCat.uliftFunctor.{w, max u v} k).map
          (ChainComplex.mixedColumnIso (bComplex k A) p n q h).hom ≫
        (bComplexMapLift f).f n ≫
          (ModuleCat.uliftFunctor.{v, max u w} k).map
            (ChainComplex.mixedColumnIso (bComplex k B) p n q h).inv := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let K := bComplex k A
  let L := bComplex k B
  let H₀A := connesBoundaryHomotopy k A
  let H₀B := connesBoundaryHomotopy k B
  let HA := connesBoundaryHomotopyLift.{u, v, w} k A
  let HB := connesBoundaryHomotopyLift.{u, w, v} k B
  let hA : ∀ j, H₀A.hom j (j + 1) ≫ H₀A.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀A]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k A j
  let hB : ∀ j, H₀B.hom j (j + 1) ≫ H₀B.hom (j + 1) (j + 2) = 0 := fun j => by
    dsimp only [H₀B]
    simpa only [connesBoundaryHomotopy_hom] using connesBoundary_square k B j
  let hcA : ∀ j, HA.hom j (j + 1) = UA.map (H₀A.hom j (j + 1)) := fun j =>
    (connesBoundaryHomotopyLift_hom k A j).trans
      (congrArg (fun a => UA.map a) (connesBoundaryHomotopy_hom k A j).symm)
  let hcB : ∀ j, HB.hom j (j + 1) = UB.map (H₀B.hom j (j + 1)) := fun j =>
    (connesBoundaryHomotopyLift_hom k B j).trans
      (congrArg (fun a => UB.map a) (connesBoundaryHomotopy_hom k B j).symm)
  change ((ChainComplex.mixedBicomplexFunctorMap UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne)).f p).f q = _
  exact ChainComplex.mixedBicomplexFunctorMap_component UA UB K L H₀A H₀B hA hB HA HB hcA hcB
    (bComplexMapLift f) (bComplexMapLift_boundary f hOne) p n q h

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. Totalization and the carrier-lift comparisons give
a chain map between the two lifted mixed totals. -/
def connesMixedTotalMapLift (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    ((ModuleCat.uliftFunctor.{w, max u v} k).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (connesMixedTotal k A) ⟶
        ((ModuleCat.uliftFunctor.{v, max u w} k).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (connesMixedTotal k B) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let RA := connesMixedBicomplex k A
  let RB := connesMixedBicomplex k B
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RA
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj RB
  letI : ∀ m, PreservesColimit (Discrete.functor
      (RA.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) UA := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  letI : ∀ m, PreservesColimit (Discrete.functor
      (RB.toGradedObject.mapObjFun (fun pq : ℕ × ℕ => pq.1 + pq.2) m)) UB := fun m => by
    letI : Fintype ((fun pq : ℕ × ℕ => pq.1 + pq.2) ⁻¹' {m}) :=
      Fintype.ofFinset (Finset.antidiagonal m) (fun pq => by
        simp only [Finset.mem_antidiagonal, Set.mem_preimage, Set.mem_singleton_iff])
    infer_instance
  let eA : (UA.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k A) ≅ PA.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.functorTotalIso UA RA
  let eB : (UB.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (connesMixedTotal k B) ≅ PB.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.functorTotalIso UB RB
  let φ : PA ⟶ PB := connesMixedBicomplexMapLift f hOne
  let m : PA.total (ComplexShape.down ℕ) ⟶ PB.total (ComplexShape.down ℕ) :=
    HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  exact eA.hom ≫ m ≫ eB.inv

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. For `2p+r=n`, the lifted supported injection followed
by the total bicomplex map equals `Φ_r` followed by the
corresponding target injection. -/
theorem connesMixedBicomplexMapLift_inclusion (f : A →ₙₐ[k] B) (hOne : f 1 = 1)
    (p r n : ℕ) (h : 2 * p + r = n) :
    mixedLevelInclusionLift.{w} k A p r n h ≫
        (HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
          (ComplexShape.down ℕ)).f n =
      (bComplexMapLift f).f r ≫ mixedLevelInclusionLift.{v} k B p r n h := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let PA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k A)
  let PB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (connesMixedBicomplex k B)
  let φ : PA ⟶ PB := connesMixedBicomplexMapLift f hOne
  let m := HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)
  let a : (PA.X p).X (r + p) ≅ UA.obj ((bComplex k A).X r) :=
    UA.mapIso (ChainComplex.mixedColumnIso (bComplex k A) p r (r + p) rfl)
  let b : (PB.X p).X (r + p) ≅ UB.obj ((bComplex k B).X r) :=
    UB.mapIso (ChainComplex.mixedColumnIso (bComplex k B) p r (r + p) rfl)
  let v : UA.obj ((bComplex k A).X r) ⟶ UB.obj ((bComplex k B).X r) :=
    (bComplexMapLift f).f r
  let ιA : (PA.X p).X (r + p) ⟶ (PA.total (ComplexShape.down ℕ)).X n :=
    PA.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  let ιB : (PB.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n :=
    PB.ιTotal (ComplexShape.down ℕ) p (r + p) n (by change p + (r + p) = n; omega)
  have hι : ιA ≫ m.f n = (φ.f p).f (r + p) ≫ ιB :=
    HomologicalComplex₂.ιTotal_map PA PB φ (ComplexShape.down ℕ)
      p (r + p) n (by change p + (r + p) = n; omega)
  have hφ : (φ.f p).f (r + p) = a.hom ≫ v ≫ b.inv :=
    connesMixedBicomplexMapLift_component f hOne p r (r + p) rfl
  change (a.inv ≫ ιA) ≫ m.f n = v ≫ (b.inv ≫ ιB)
  calc
    (a.inv ≫ ιA) ≫ m.f n = a.inv ≫ (ιA ≫ m.f n) := Category.assoc _ _ _
    _ = a.inv ≫ ((φ.f p).f (r + p) ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n =>
        a.inv ≫ x) hι
    _ = a.inv ≫ ((a.hom ≫ v ≫ b.inv) ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.X p).X (r + p) =>
        a.inv ≫ (x ≫ ιB)) hφ
    _ = a.inv ≫ (a.hom ≫ v ≫ b.inv ≫ ιB) :=
      congrArg (fun x : (PA.X p).X (r + p) ⟶ (PB.total (ComplexShape.down ℕ)).X n =>
        a.inv ≫ x)
        ((Category.assoc a.hom (v ≫ b.inv) ιB).trans
          (congrArg (fun x : UA.obj ((bComplex k A).X r) ⟶
              (PB.total (ComplexShape.down ℕ)).X n => a.hom ≫ x)
            (Category.assoc v b.inv ιB)))
    _ = v ≫ b.inv ≫ ιB := a.inv_hom_id_assoc (v ≫ b.inv ≫ ιB)


omit [IsScalarTower k A A] [SMulCommClass k A A]
  [IsScalarTower k B B] [SMulCommClass k B B] in
/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. The lifted norm and insertion satisfy
`Φ_n ≫ N_B,n ≫ s_B,n = N_A,n ≫ s_A,n ≫ Φ_(n+1)`;
unit preservation identifies the transported insertion vector
with `1_B`. -/
theorem normInsertMapLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) (n : ℕ) :
    levelMapLift (f : A →ₗ[k] B) n ≫
        (ModuleCat.uliftFunctor.{v, max u w} k).map (normMap k B n) ≫
          (ModuleCat.uliftFunctor.{v, max u w} k).map (extraDegeneracy k B n) =
      (ModuleCat.uliftFunctor.{w, max u v} k).map (normMap k A n) ≫
        (ModuleCat.uliftFunctor.{w, max u v} k).map (extraDegeneracy k A n) ≫
          levelMapLift (f : A →ₗ[k] B) (n + 1) := by
  have hVector : (f : A →ₗ[k] B) (1 : A) = (1 : B) := hOne
  simpa only [extraDegeneracy, hVector, Functor.map_comp, Category.assoc] using
    normInsertWithMapLift_naturality (f : A →ₗ[k] B) (1 : A) n

/-- Let `k` be a commutative ring, `A,B` unital rings with compatible
central `k`-actions, and `f : A →ₙₐ[k] B` satisfy `f(1_A)=1_B`.
Lift the two models to the common height `max(u,v,w)`.
Write `Φ_n` for the degree-`n` full Hochschild word map of `f`. The comparison maps satisfy the chain square
`Tot(f_mix) ≫ i_B = i_A ≫ Tot(f_cyc)` in the common carrier
height, with the two positive mixed-to-cyclic comparisons. -/
theorem mixedToCyclicLift_naturality (f : A →ₙₐ[k] B) (hOne : f 1 = 1) :
    HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
        (ComplexShape.down ℕ) ≫ mixedToCyclicLift.{v} k B =
      mixedToCyclicLift.{w} k A ≫
        HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ) := by
  let UA := ModuleCat.uliftFunctor.{w, max u v} k
  let UB := ModuleCat.uliftFunctor.{v, max u w} k
  let CA : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UA.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k A)
  let CB : HomologicalComplex₂ (ModuleCat.{max u v w} k)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
      ((UB.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cyclicBicomplex k B)
  let m := HomologicalComplex₂.total.map (connesMixedBicomplexMapLift f hOne)
    (ComplexShape.down ℕ)
  let c := HomologicalComplex₂.total.map (cyclicBicomplexMap f) (ComplexShape.down ℕ)
  let I := mixedToCyclicLift.{w} k A
  let I' := mixedToCyclicLift.{v} k B
  apply HomologicalComplex.hom_ext
  intro n
  apply connesMixedTotalLift_hom_ext.{w} k A n
  intro p r h
  let ιA := mixedLevelInclusionLift.{w} k A p r n h
  let ιB := mixedLevelInclusionLift.{v} k B p r n h
  let evenA : UA.obj (chainLevel k A A r) ⟶
      (CA.total (ComplexShape.down ℕ)).X n :=
    CA.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddA : UA.obj (chainLevel k A A (r + 1)) ⟶
      (CA.total (ComplexShape.down ℕ)).X n :=
    CA.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let evenB : UB.obj (chainLevel k B B r) ⟶
      (CB.total (ComplexShape.down ℕ)).X n :=
    CB.ιTotalOrZero (ComplexShape.down ℕ) (2 * p) r n
  let oddB : UB.obj (chainLevel k B B (r + 1)) ⟶
      (CB.total (ComplexShape.down ℕ)).X n :=
    CB.ιTotalOrZero (ComplexShape.down ℕ) (2 * p - 1) (r + 1) n
  let a := levelMapLift (f : A →ₗ[k] B) r
  let a' := levelMapLift (f : A →ₗ[k] B) (r + 1)
  let NA := UA.map (normMap k A r)
  let NB := UB.map (normMap k B r)
  let sA := UA.map (extraDegeneracy k A r)
  let sB := UB.map (extraDegeneracy k B r)
  have hI : ιA ≫ I.f n = evenA + NA ≫ sA ≫ oddA :=
    mixedToCyclicLift_inclusion k A p r n h
  have hI' : ιB ≫ I'.f n = evenB + NB ≫ sB ≫ oddB :=
    mixedToCyclicLift_inclusion k B p r n h
  have hm : ιA ≫ m.f n = a ≫ ιB :=
    (connesMixedBicomplexMapLift_inclusion f hOne p r n h).trans
      (congrArg (fun x => x ≫ ιB) (bComplexMapLift_f f r))
  have he : evenA ≫ c.f n = a ≫ evenB := cyclicBicomplexMap_ιTotalOrZero f (2 * p) r n
  have ho : oddA ≫ c.f n = a' ≫ oddB :=
    cyclicBicomplexMap_ιTotalOrZero f (2 * p - 1) (r + 1) n
  have hSN : a ≫ NB ≫ sB = NA ≫ sA ≫ a' := normInsertMapLift_naturality f hOne r
  have hPost : NA ≫ sA ≫ (a' ≫ oddB) = a ≫ NB ≫ sB ≫ oddB := by
    calc
      NA ≫ sA ≫ (a' ≫ oddB) = (NA ≫ sA ≫ a') ≫ oddB := by
        simp only [Category.assoc]
      _ = (a ≫ NB ≫ sB) ≫ oddB :=
        congrArg (fun x : UA.obj (chainLevel k A A r) ⟶
          UB.obj (chainLevel k B B (r + 1)) => x ≫ oddB) hSN.symm
      _ = a ≫ NB ≫ sB ≫ oddB := by
        simp only [Category.assoc]
  have hLeft : ιA ≫ (m.f n ≫ I'.f n) =
      a ≫ evenB + a ≫ NB ≫ sB ≫ oddB := by
    calc
      _ = (a ≫ ιB) ≫ I'.f n :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ I'.f n) hm)
      _ = a ≫ (evenB + NB ≫ sB ≫ oddB) :=
        (Category.assoc _ _ _).trans (congrArg (fun x => a ≫ x) hI')
      _ = _ := by simp only [Preadditive.comp_add, Category.assoc]
  have hRight : ιA ≫ (I.f n ≫ c.f n) =
      a ≫ evenB + a ≫ NB ≫ sB ≫ oddB := by
    calc
      _ = (evenA + NA ≫ sA ≫ oddA) ≫ c.f n :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ c.f n) hI)
      _ = evenA ≫ c.f n + NA ≫ sA ≫ (oddA ≫ c.f n) := by
        simp only [Preadditive.add_comp, Category.assoc]
      _ = a ≫ evenB + NA ≫ sA ≫ (a' ≫ oddB) :=
        congrArg₂ (fun x y => x + y) he (congrArg (fun x => NA ≫ sA ≫ x) ho)
      _ = _ := congrArg (fun x => a ≫ evenB + x) hPost
  change ιA ≫ (m.f n ≫ I'.f n) = ιA ≫ (I.f n ≫ c.f n)
  exact hLeft.trans hRight.symm

end MixedNaturality

end ModuleCat.Algebra.Hochschild.NonUnital

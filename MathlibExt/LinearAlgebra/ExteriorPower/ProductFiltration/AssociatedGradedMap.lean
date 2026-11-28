/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductFiltration.Triangular

/-!
# Associated-graded maps of first-summand-preserving exterior operators

Let f : M × N →ₗ[R] M' × N' be a linear map over a commutative ring, with a map a : M →ₗ[R] M'
satisfying f ∘ inl = inl' ∘ a. Put b = snd' ∘ f ∘ inr : N →ₗ[R] N'. The exterior map ⋀^m f
preserves every mixed-weight stage F_m^q and therefore induces a map of its adjacent-stage
quotient.

For q ≤ m, the quotient coordinate of this map is TensorProduct.map (⋀^q a) (⋀^(m−q) b). The
component of f from N into M' contributes only in higher first weight and vanishes modulo
F_m^(q+1). This description holds for arbitrary modules and is compatible with identities and
composition.

See Bourbaki, *Algebra*, Chapter III, for exterior powers of direct sums.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w v' w' v'' w''

namespace exteriorPower.ProductFiltration

variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]

-- Use the canonical native subgroup data with its scalar and carrier explicit.
local instance (X : Type*) [AddCommGroup X] [Module R X] (m : ℕ) :
    AddCommGroup (⋀[R]^m X) :=
  Submodule.addCommGroup (R := R) (M := ExteriorAlgebra R X)
    (ExteriorAlgebra.exteriorPower R m X)

local instance (m q : ℕ) : AddCommGroup (filtration R M N m q) :=
  Submodule.addCommGroup (R := R) (M := ⋀[R]^m (M × N))
    (filtration R M N m q)


/-- Let R be a commutative ring and M and N R-modules. In exterior degree m, let F_m^q consist of
elements whose mixed coordinates of first degree below q are zero. For q ≤ m, mixedClass R M N
m q hq is the R-linear map from ⋀[R]^q M ⊗[R] ⋀[R]^(m−q) N to F_m^q/nextStage obtained by
applying gradeSection and then the quotient projection. Its composite with
associatedGradedEquiv is the identity on the mixed tensor piece. -/
def mixedClass (m q : ℕ) (hq : q ≤ m) :
    Piece R M N m (index m q hq) →ₗ[R] associatedGraded R M N m q :=
  by
    let s : Piece R M N m (index m q hq) →ₗ[R] filtration R M N m q :=
      gradeSection R M N m q hq
    let π : filtration R M N m q →ₗ[R] associatedGraded R M N m q :=
      Submodule.mkQ (R := R) (M := filtration R M N m q) (nextStage R M N m q)
    exact π.comp s

theorem associatedGradedEquiv_mixedClass (m q : ℕ) (hq : q ≤ m)
    (z : Piece R M N m (index m q hq)) :
    associatedGradedEquiv R M N m q hq (mixedClass R M N m q hq z) = z := by
  change associatedGradedEquiv R M N m q hq
    (Submodule.Quotient.mk (p := nextStage R M N m q)
      (gradeSection R M N m q hq z)) = z
  rw [associatedGradedEquiv_mk]
  exact gradeProjection_section R M N m q hq z

theorem mixedClass_surjective (m q : ℕ) (hq : q ≤ m) :
    Function.Surjective (mixedClass R M N m q hq) := by
  intro z
  let t : Piece R M N m (index m q hq) := associatedGradedEquiv R M N m q hq z
  refine ⟨t, ?_⟩
  apply (associatedGradedEquiv R M N m q hq).injective
  exact associatedGradedEquiv_mixedClass R M N m q hq t

end exteriorPower.ProductFiltration

namespace exteriorPower.ProductFiltration.FirstSummandMap

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {M' : Type v'} [AddCommGroup M'] [Module R M']
  {N' : Type w'} [AddCommGroup N'] [Module R N']
  (f : FirstSummandMap (R := R) (M := M) (N := N) (M' := M') (N' := N'))

-- Both native stage subgroups retain the given source and target module worlds.
local instance (X : Type*) [AddCommGroup X] [Module R X] (m : ℕ) :
    AddCommGroup (⋀[R]^m X) :=
  Submodule.addCommGroup (R := R) (M := ExteriorAlgebra R X)
    (ExteriorAlgebra.exteriorPower R m X)

local instance (m q : ℕ) : AddCommGroup (filtration R M N m q) :=
  Submodule.addCommGroup (R := R) (M := ⋀[R]^m (M × N))
    (filtration R M N m q)

local instance (m q : ℕ) : AddCommGroup (filtration R M' N' m q) :=
  Submodule.addCommGroup (R := R) (M := ⋀[R]^m (M' × N'))
    (filtration R M' N' m q)


/-- Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For m, q : ℕ, stageMap restricts ⋀^m f.map to a linear map F_m^q(M, N) → F_m^q(M', N'),
where the stages are defined by vanishing of mixed coordinates of first weight below q. -/
def stageMap (m q : ℕ) :
    filtration R M N m q →ₗ[R] filtration R M' N' m q :=
  ((exteriorPower.map m f.map).domRestrict (filtration R M N m q)).codRestrict
    (filtration R M' N' m q) (fun z => f.map_mem_filtration m q z.val z.property)

/-- Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For every m, q : ℕ, nextStage R M N m q ≤ (nextStage R M' N' m q).comap (f.stageMap m q).
Thus the restricted exterior map sends the next stage inside the source stage to the
corresponding next target stage. -/
theorem stageMap_next (m q : ℕ) :
    nextStage R M N m q ≤
      (nextStage R M' N' m q).comap (f.stageMap m q) := by
  intro z hz
  exact f.map_mem_filtration m (q + 1) z.val hz

/-- Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For m, q : ℕ, f.gradeMap m q is the R-linear map F_m^q(M, N)/F_m^(q+1)(M, N) → F_m^q(M',
N')/F_m^(q+1)(M', N') induced by f.stageMap and its preservation of the next-stage submodules. -/
def gradeMap (m q : ℕ) :
    associatedGraded R M N m q →ₗ[R] associatedGraded R M' N' m q :=
  by
    let g : filtration R M N m q →ₗ[R] filtration R M' N' m q := f.stageMap m q
    let h : nextStage R M N m q ≤ (nextStage R M' N' m q).comap g := f.stageMap_next m q
    exact Submodule.mapQ (R := R) (R₂ := R)
      (M := filtration R M N m q) (M₂ := filtration R M' N' m q)
      (nextStage R M N m q) (nextStage R M' N' m q) g h

theorem gradeMap_mk (m q : ℕ) (z : filtration R M N m q) :
    f.gradeMap m q (Submodule.Quotient.mk (p := nextStage R M N m q) z) =
      Submodule.Quotient.mk (p := nextStage R M' N' m q) (f.stageMap m q z) := by
  rw [gradeMap, Submodule.mapQ_apply]

/-- Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For q ≤ m, x : ⋀[R]^q M and y : ⋀[R]^(m−q) N, f.gradeMap sends mixedClass(x ⊗ y) to
mixedClass'(⋀^q f.first(x) ⊗ ⋀^(m−q) f.relative(y)). Terms from the N-to-M' component of f lie
in stage q + 1 and are zero in this quotient. -/
theorem gradeMap_mixed_tmul (m q : ℕ) (hq : q ≤ m)
    (x : ⋀[R]^q M) (y : ⋀[R]^(m - q) N) :
    f.gradeMap m q (mixedClass R M N m q hq (x ⊗ₜ[R] y)) =
      mixedClass R M' N' m q hq
        (exteriorPower.map q f.first x ⊗ₜ[R] exteriorPower.map (m - q) f.relative y) := by
  let z : filtration R M N m q := gradeSection R M N m q hq (x ⊗ₜ[R] y)
  let z' : filtration R M' N' m q := gradeSection R M' N' m q hq
    (exteriorPower.map q f.first x ⊗ₜ[R] exteriorPower.map (m - q) f.relative y)
  have hd : f.stageMap m q z - z' ∈ nextStage R M' N' m q := by
    change exteriorPower.map m f.map
        (injection R M N m (index m q hq) (x ⊗ₜ[R] y)) -
      injection R M' N' m (index m q hq)
        (exteriorPower.map q f.first x ⊗ₜ[R] exteriorPower.map (m - q) f.relative y) ∈
          filtration R M' N' m (q + 1)
    exact f.mixed_difference_mem_next_of_index m (index m q hq) x y
  have hp : gradeProjection R M' N' m q hq (f.stageMap m q z - z') = 0 := by
    change f.stageMap m q z - z' ∈ (gradeProjection R M' N' m q hq).ker
    rw [gradeProjection_ker]
    exact hd
  have hsub : gradeProjection R M' N' m q hq (f.stageMap m q z - z') =
      gradeProjection R M' N' m q hq (f.stageMap m q z) - gradeProjection R M' N' m q hq z' :=
    by
      change coordinate R M' N' m (index m q hq)
          ((f.stageMap m q z).val - z'.val) =
        coordinate R M' N' m (index m q hq) (f.stageMap m q z).val -
          coordinate R M' N' m (index m q hq) z'.val
      exact map_sub (coordinate R M' N' m (index m q hq)) (f.stageMap m q z).val z'.val
  have hcoordinate : gradeProjection R M' N' m q hq (f.stageMap m q z) =
      gradeProjection R M' N' m q hq z' := sub_eq_zero.mp (hsub.symm.trans hp)
  let e := associatedGradedEquiv R M' N' m q hq
  have hleft : e (f.gradeMap m q (mixedClass R M N m q hq (x ⊗ₜ[R] y))) =
      gradeProjection R M' N' m q hq (f.stageMap m q z) :=
    (congrArg e (gradeMap_mk f m q z)).trans
      (associatedGradedEquiv_mk R M' N' m q hq (f.stageMap m q z))
  have hright : e (mixedClass R M' N' m q hq
      (exteriorPower.map q f.first x ⊗ₜ[R] exteriorPower.map (m - q) f.relative y)) =
        gradeProjection R M' N' m q hq z' :=
    associatedGradedEquiv_mk R M' N' m q hq z'
  exact e.injective (hleft.trans (hcoordinate.trans hright.symm))

/-- Let R be a commutative ring and M, N, M', N' R-modules. Let f.map : M × N →ₗ[R] M' × N' and
f.first : M →ₗ[R] M' satisfy f.map ∘ inl = inl' ∘ f.first. Put f.relative = snd' ∘ f.map ∘
inr. For q ≤ m and a source associated-grade class z, let E_q and E'_q be the complementary
mixed-tensor coordinate equivalences. Then E'_q(f.gradeMap m q z) = TensorProduct.map
(exteriorPower.map q f.first) (exteriorPower.map (m − q) f.relative) (E_q(z)). -/
theorem associatedGradedEquiv_gradeMap (m q : ℕ) (hq : q ≤ m)
    (z : associatedGraded R M N m q) :
    associatedGradedEquiv R M' N' m q hq (f.gradeMap m q z) =
      TensorProduct.map (exteriorPower.map q f.first) (exteriorPower.map (m - q) f.relative)
        (associatedGradedEquiv R M N m q hq z) := by
  let l : (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) →ₗ[R]
      (⋀[R]^q M') ⊗[R] (⋀[R]^(m - q) N') :=
    (associatedGradedEquiv R M' N' m q hq).toLinearMap.comp
      ((f.gradeMap m q).comp (mixedClass R M N m q hq))
  let r : (⋀[R]^q M) ⊗[R] (⋀[R]^(m - q) N) →ₗ[R]
      (⋀[R]^q M') ⊗[R] (⋀[R]^(m - q) N') :=
    TensorProduct.map (exteriorPower.map q f.first) (exteriorPower.map (m - q) f.relative)
  have h : l = r := by
    apply TensorProduct.ext'
    intro x y
    change associatedGradedEquiv R M' N' m q hq
        (f.gradeMap m q (mixedClass R M N m q hq (x ⊗ₜ[R] y))) = r (x ⊗ₜ[R] y)
    have hmap := gradeMap_mixed_tmul f m q hq x y
    have hgrade := associatedGradedEquiv_mixedClass R M' N' m q hq
      (exteriorPower.map q f.first x ⊗ₜ[R] exteriorPower.map (m - q) f.relative y)
    exact (congrArg (associatedGradedEquiv R M' N' m q hq) hmap).trans
      (hgrade.trans (TensorProduct.map_tmul _ _ x y).symm)
  obtain ⟨t, ht⟩ := mixedClass_surjective R M N m q hq z
  have hvalue : associatedGradedEquiv R M' N' m q hq
      (f.gradeMap m q (mixedClass R M N m q hq t)) = r t := LinearMap.congr_fun h t
  have hsource : associatedGradedEquiv R M N m q hq z = t :=
    (congrArg (associatedGradedEquiv R M N m q hq) ht.symm).trans
      (associatedGradedEquiv_mixedClass R M N m q hq t)
  exact (congrArg (fun a => associatedGradedEquiv R M' N' m q hq (f.gradeMap m q a)) ht.symm).trans
    (hvalue.trans (congrArg r hsource).symm)

theorem stageMap_id (m q : ℕ) :
    (FirstSummandMap.id (R := R) (M := M) (N := N)).stageMap m q = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change exteriorPower.map m LinearMap.id z.val = z.val
  rw [exteriorPower.map_id, LinearMap.id_apply]

theorem gradeMap_id (m q : ℕ) :
    (FirstSummandMap.id (R := R) (M := M) (N := N)).gradeMap m q = LinearMap.id := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on (nextStage R M N m q) z (fun x => ?_)
  rw [gradeMap_mk, stageMap_id, LinearMap.id_apply]
  rfl

variable {M'' : Type v''} [AddCommGroup M''] [Module R M'']
  {N'' : Type w''} [AddCommGroup N''] [Module R N'']

theorem stageMap_comp
    (g : FirstSummandMap (R := R) (M := M') (N := N') (M' := M'') (N' := N'')) (m q : ℕ) :
    (f.comp g).stageMap m q = (g.stageMap m q).comp (f.stageMap m q) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change exteriorPower.map m (g.map.comp f.map) z.val =
    exteriorPower.map m g.map (exteriorPower.map m f.map z.val)
  rw [exteriorPower.map_comp, LinearMap.comp_apply]

theorem gradeMap_comp
    (g : FirstSummandMap (R := R) (M := M') (N := N') (M' := M'') (N' := N'')) (m q : ℕ) :
    (f.comp g).gradeMap m q = (g.gradeMap m q).comp (f.gradeMap m q) := by
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on (nextStage R M N m q) z (fun x => ?_)
  rw [gradeMap_mk, LinearMap.comp_apply, gradeMap_mk, gradeMap_mk, stageMap_comp]
  rfl

end exteriorPower.ProductFiltration.FirstSummandMap

end

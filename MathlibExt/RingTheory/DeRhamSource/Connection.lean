/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/Connection.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: module paths and outer namespace are adapted for Atlas; source-only documentation
cross-reference attributes are omitted. All original mathematical proof bodies are retained.
-/

public import MathlibExt.RingTheory.DeRhamSource.Basic

namespace MathlibExt.DeRhamSource

open _root_.Algebra _root_.KaehlerDifferential

/-!
# Connections, their extension to differential forms, and integrability

Let `A → B` be a map of commutative rings, let `π : Ω[B⁄A] → Ω` be a map of `B`-modules — in the
applications a surjection along which the de Rham differential descends, as in Tag 07HY — and let
`M` be a `B`-module.  A *connection* on `M` relative to `π` is an additive map
`∇ : M → M ⊗[B] Ω` subject to the Leibniz rule

`∇ (b • m) = b • ∇ m + m ⊗ π (d b)`,

where `d = KaehlerDifferential.D A B`.  A connection is additive but not in general `B`-linear,
which is why it is bundled as an `AddMonoidHom` together with its Leibniz property.

Once the de Rham differential descends to a family `dΩ : ⋀^p Ω → ⋀^{p+1} Ω`, a connection extends
in every degree to a map

`M ⊗[B] ⋀^p Ω → M ⊗[B] ⋀^{p+1} Ω`, `m ⊗ ω ↦ (∇ m) ∧ ω + m ⊗ dΩ ω`,

the wedge being taken on the `Ω`-factor of `∇ m` by left exterior multiplication.  The extension
exists because the displayed formula is balanced: the Leibniz rules for `∇` and for `dΩ` cancel
each other when a scalar `b : B` is moved across the tensor sign.  Since `dΩ` is `A`-linear and
not in general `B`-linear, the terms are viewed as `A`-modules by restriction of scalars along `A → B`,
matching `Stacks.DeRham.DifferentialDescent.TgtA`.

Finally, the connection is *integrable* when its composite with its own degree-one extension
vanishes.  This is the vanishing of the curvature, and it is exactly the hypothesis under which
the extensions form a complex.

## Main definitions

* `Crystalline.Connection` — a connection on a module relative to a map `Ω[B⁄A] →ₗ[B] Ω`.
* `Crystalline.leftWedge` — left exterior multiplication by a one-form, as a bilinear map.
* `Crystalline.ExtendedConnection` — a descended de Rham differential together with the extension
  of a connection to all degrees, and the formula for it on pure tensors.
* `Crystalline.extendedConnection` — the canonical such extension.
* `Crystalline.Connection.IsIntegrable` — vanishing of the curvature of a connection.

## Main results

* `Crystalline.Connection.leibniz` — the Leibniz rule for a connection.
* `Crystalline.span_range_ιMulti_eq_top`, `Crystalline.span_range_smul_ιMulti_eq_top` — the wedges
  of a spanning family span the exterior powers, over the ring of scalars and already over a base
  ring of it.
* `Crystalline.Connection.isIntegrable_iff_comp_eq_zero` — integrability as the vanishing of the
  displayed composite.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

namespace Crystalline

/-! ### Wedges in the exterior algebra -/

section Wedges

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A wedge of length one is the vector itself, read in the exterior algebra. -/
public lemma coe_ιMulti_one (x : M) :
    (exteriorPower.ιMulti R 1 (fun _ ↦ x) : ExteriorAlgebra R M) = ExteriorAlgebra.ι R x := by
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  simp

/-- Splitting off the first entry of a wedge multiplies by it, read in the exterior algebra. -/
public lemma coe_ιMulti_succ (p : ℕ) (f : Fin (p + 1) → M) :
    (exteriorPower.ιMulti R (p + 1) f : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R (f 0) *
        (exteriorPower.ιMulti R p (fun i ↦ f i.succ) : ExteriorAlgebra R M) := by
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
  have hf : (fun i : Fin (p + 1) ↦ ExteriorAlgebra.ι R (f i)) =
      Fin.cons (ExteriorAlgebra.ι R (f 0)) (fun i ↦ ExteriorAlgebra.ι R (f i.succ)) := by
    funext i
    cases i using Fin.cases <;> simp
  rw [hf, List.ofFn_cons, List.prod_cons, ← ExteriorAlgebra.ιMulti_apply,
    exteriorPower.ιMulti_apply_coe]

end Wedges

section LeftWedge

variable {B Omega : Type*} [CommRing B] [AddCommGroup Omega] [Module B Omega]

/-- Left exterior multiplication by a one-form, as a bilinear map. -/
public noncomputable def leftWedge (p : ℕ) :
    Omega →ₗ[B] (⋀[B]^p Omega) →ₗ[B] (⋀[B]^(p + 1) Omega) :=
  LinearMap.mk₂ B
    (fun x y ↦ ⟨ExteriorAlgebra.ι B x * (y : ExteriorAlgebra B Omega), by
      rw [add_comm]
      exact SetLike.mul_mem_graded
        (show ExteriorAlgebra.ι B x ∈ ⋀[B]^1 Omega by
          simpa only [pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι B) x)
        y.2⟩)
    (fun x₁ x₂ y ↦ Subtype.ext (by push_cast; rw [map_add, add_mul]))
    (fun c x y ↦ Subtype.ext (by push_cast; rw [map_smul, smul_mul_assoc]))
    (fun x y₁ y₂ ↦ Subtype.ext (by push_cast; rw [mul_add]))
    (fun c x y ↦ Subtype.ext (by push_cast; rw [mul_smul_comm]))

/-- Left exterior multiplication agrees with multiplication in the exterior algebra. -/
@[simp]
public theorem leftWedge_coe (p : ℕ) (x : Omega) (y : ⋀[B]^p Omega) :
    (leftWedge p x y : ExteriorAlgebra B Omega) =
      ExteriorAlgebra.ι B x * (y : ExteriorAlgebra B Omega) :=
  rfl

/-- Left exterior multiplication by `a` turns the wedge `v₁ ∧ ⋯ ∧ v_p` into `a ∧ v₁ ∧ ⋯ ∧ v_p`. -/
public theorem leftWedge_ιMulti (p : ℕ) (a : Omega) (v : Fin p → Omega) :
    leftWedge p a (exteriorPower.ιMulti B p v) =
      exteriorPower.ιMulti B (p + 1) (Fin.cons a v) := by
  apply Subtype.ext
  rw [leftWedge_coe, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, Fin.cons_zero]
  rfl

end LeftWedge

/-! ### Spanning sets of the exterior powers -/

section Span

/-- The wedges `D c₁ ∧ ⋯ ∧ D c_p` of values of a map `D : S → M` whose range spans `M` over `S`
span the `p`-th exterior power `⋀[S]^p M` over `S`. -/
public lemma span_range_ιMulti_eq_top {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    (D : S → M) (hD : Submodule.span S (Set.range D) = ⊤) (p : ℕ) :
    Submodule.span S (Set.range fun c : Fin p → S ↦
      exteriorPower.ιMulti S p fun i ↦ D (c i)) = ⊤ := by
  have himg : exteriorPower.ιMulti S p '' {a : Fin p → M | Set.range a ⊆ Set.range D} =
      Set.range fun c : Fin p → S ↦ exteriorPower.ιMulti S p fun i ↦ D (c i) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      choose c hc using fun i ↦ ha (Set.mem_range_self i)
      exact ⟨c, congrArg _ (funext hc)⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨_, Set.range_subset_iff.2 fun i ↦ ⟨c i, rfl⟩, rfl⟩
  rw [← himg, exteriorPower.ιMulti_span_of_span S p M hD]

open Pointwise in
/-- The elements `c₀ · (D c₁ ∧ ⋯ ∧ D c_p)` span `⋀[S]^p M` already as a module over a base ring
`R` of `S`, not merely over `S`: they are `S • {D c₁ ∧ ⋯ ∧ D c_p}`, and multiplying an
`S`-spanning set by all of `S` produces an `R`-spanning set. -/
public lemma span_range_smul_ιMulti_eq_top {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (D : S → M) (hD : Submodule.span S (Set.range D) = ⊤) (p : ℕ) :
    Submodule.span R (Set.range fun c : Fin (p + 1) → S ↦
      c 0 • exteriorPower.ιMulti S p fun i ↦ D (c i.succ)) = ⊤ := by
  have hset : (Set.univ : Set S) • (Set.range fun c : Fin p → S ↦
        exteriorPower.ιMulti S p fun i ↦ D (c i)) =
      Set.range fun c : Fin (p + 1) → S ↦
        c 0 • exteriorPower.ιMulti S p fun i ↦ D (c i.succ) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨x, -, _, ⟨c, rfl⟩, rfl⟩
      exact ⟨Fin.cons x c, by simp⟩
    · rintro _ ⟨c, rfl⟩
      exact Set.smul_mem_smul (Set.mem_univ _) ⟨fun i ↦ c i.succ, rfl⟩
  rw [← hset, Submodule.span_smul_of_span_eq_top Submodule.span_univ,
    span_range_ιMulti_eq_top D hD, Submodule.restrictScalars_top]

end Span

/-! ### The de Rham differentials, read on the exterior powers -/

section Differentials

open Stacks.DeRham.DifferentialDescent

universe u

section Source

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The de Rham differential of `B` over `A` carried by `S`, read as an additive map between the
exterior powers themselves rather than between their `RestrictScalars` synonyms
`Stacks.DeRham.DifferentialDescent.SrcA`.  Spelling the synonyms out is what keeps a goal
mentioning the differential type-correct: `SrcA A B q` and `⋀[B]^q Ω[B⁄A]` are equal only after
unfolding `RestrictScalars`. -/
public noncomputable def sourceDifferential (S : SourceDeRham A B) (q : ℕ) :
    (⋀[B]^q (Ω[B⁄A])) →+ (⋀[B]^(q + 1) (Ω[B⁄A])) where
  toFun y := RestrictScalars.addEquiv A B _ (S.d q ((RestrictScalars.addEquiv A B _).symm y))
  map_zero' := by simp
  map_add' x y := by simp

/-- The defining rule of the de Rham differential, on the generators
`b₀ · (d b₁ ∧ ⋯ ∧ d b_q)`. -/
public lemma sourceDifferential_srcGen (S : SourceDeRham A B) (q : ℕ) (f : Fin (q + 1) → B) :
    sourceDifferential S q (srcGen q f) = srcGenRes q f := S.gen q f

/-- The de Rham differential of `B` over `A` is a complex. -/
public lemma sourceDifferential_comp_self (S : SourceDeRham A B) (q : ℕ)
    (x : ⋀[B]^q (Ω[B⁄A])) :
    sourceDifferential S (q + 1) (sourceDifferential S q x) = 0 := by
  have h := LinearMap.congr_fun (S.complex q)
    ((RestrictScalars.addEquiv A B (⋀[B]^q (Ω[B⁄A]))).symm x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact h

end Source

section Target

variable {A B Omega : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega]

/-- A candidate family of descended differentials, read as an additive map between the exterior
powers themselves rather than between their `RestrictScalars` synonyms
`Stacks.DeRham.DifferentialDescent.TgtA`. -/
public noncomputable def descendedDifferential
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1)) (p : ℕ) :
    (⋀[B]^p Omega) →+ (⋀[B]^(p + 1) Omega) where
  toFun ω := RestrictScalars.addEquiv A B _ (dΩ p ((RestrictScalars.addEquiv A B _).symm ω))
  map_zero' := by simp
  map_add' x y := by simp

/-- `descendedDifferential dΩ p` applies `dΩ p` to a form, read through the `RestrictScalars`
synonyms on both sides. -/
public lemma descendedDifferential_apply
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1)) (p : ℕ) (ω : ⋀[B]^p Omega) :
    descendedDifferential dΩ p ω = RestrictScalars.addEquiv A B _ (dΩ p ω) := rfl

/-- The squares of Tag 07HY, read on the exterior powers: a candidate family of descended
differentials commutes with `⋀^p π` precisely when it agrees with the de Rham differential of
`B` over `A` after applying `⋀^p π`. -/
public lemma descendedDifferential_commutes (S : SourceDeRham A B) (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1)) (hcomm : S.Commutes π dΩ)
    (p : ℕ) (x : ⋀[B]^p (Ω[B⁄A])) :
    descendedDifferential dΩ p (exteriorPower.map p π x) =
      exteriorPower.map (p + 1) π (sourceDifferential S p x) :=
  hcomm p x

end Target

end Differentials

/-! ### Connections -/

section Defs

open scoped TensorProduct

/-- An additive connection on a `B`-module `M` relative to a map from the Kähler
differentials of `B` over `A` to a `B`-module `Ω`. -/
public structure Connection
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    {Omega : Type*} [AddCommGroup Omega] [Module B Omega]
    (pi : Ω[B⁄A] →ₗ[B] Omega)
    (M : Type*) [AddCommGroup M] [Module B M] where
  /-- The underlying additive map of a connection. -/
  toAddMonoidHom : M →+ (M ⊗[B] Omega)
  /-- The Leibniz rule for a connection. -/
  leibniz' : ∀ (b : B) (m : M),
    toAddMonoidHom (b • m) =
      b • toAddMonoidHom m + m ⊗ₜ[B] pi (KaehlerDifferential.D A B b)

namespace Connection

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {Omega : Type*} [AddCommGroup Omega] [Module B Omega]
  {pi : Ω[B⁄A] →ₗ[B] Omega}
  {M : Type*} [AddCommGroup M] [Module B M]

/-- A connection coerces to its underlying function. -/
public instance : CoeFun (Connection A B pi M) (fun _ ↦ M → M ⊗[B] Omega) where
  coe nabla := nabla.toAddMonoidHom

/-- Connections preserve zero. -/
@[simp]
public theorem map_zero (nabla : Connection A B pi M) : nabla 0 = 0 :=
  nabla.toAddMonoidHom.map_zero

/-- Connections preserve addition. -/
@[simp]
public theorem map_add (nabla : Connection A B pi M) (m n : M) :
    nabla (m + n) = nabla m + nabla n :=
  nabla.toAddMonoidHom.map_add m n

/-- The Leibniz rule for a connection. -/
public theorem leibniz (nabla : Connection A B pi M) (b : B) (m : M) :
    nabla (b • m) =
      b • nabla m + m ⊗ₜ[B] pi (KaehlerDifferential.D A B b) :=
  nabla.leibniz' b m

/-- Two connections are equal if they agree on every element. -/
@[ext]
public theorem ext {nabla nabla' : Connection A B pi M}
    (h : ∀ m, nabla m = nabla' m) : nabla = nabla' := by
  cases nabla; cases nabla'; congr 1; exact AddMonoidHom.ext h

end Connection

end Defs

/-! ### Extending a connection to differential forms -/

section Extended

open scoped TensorProduct

open Stacks.DeRham.DifferentialDescent

universe u v

variable {A B Omega : Type u} {M : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup M] [Module B M]

/-- The values of the descended differential `d = π ∘ D` span the target `Omega` over `B`, since
the universal derivation spans `Ω[B⁄A]` and `π` is surjective. -/
public theorem targetD_span (π : Ω[B⁄A] →ₗ[B] Omega)
    (hπ : Function.Surjective π) :
    Submodule.span B (Set.range (SourceDeRham.targetD π)) = ⊤ := by
  have heq : Set.range (SourceDeRham.targetD π) =
      π '' Set.range (KaehlerDifferential.D A B) := Set.range_comp _ _
  rw [heq, ← Submodule.map_span, KaehlerDifferential.span_range_derivation,
    Submodule.map_top, LinearMap.range_eq_top.mpr hπ]

open Pointwise in
private theorem targetFormGenerators_span
    (π : Ω[B⁄A] →ₗ[B] Omega) (hπ : Function.Surjective π) (p : ℕ)
    [Module A Omega] [IsScalarTower A B Omega] :
    Submodule.span A
      (Set.range fun b : Fin (p + 1) → B =>
        b 0 • exteriorPower.ιMulti B p fun i => SourceDeRham.targetD π (b i.succ)) = ⊤ :=
  span_range_smul_ιMulti_eq_top (R := A) (SourceDeRham.targetD π) (targetD_span π hπ) p

private theorem descendedDifferential_leibniz
    (π : Ω[B⁄A] →ₗ[B] Omega) (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ) (p : ℕ)
    [Module A Omega] [IsScalarTower A B Omega] (b : B)
    (ω : ⋀[B]^p Omega) :
    descendedDifferential dΩ p (b • ω) =
      b • descendedDifferential dΩ p ω + leftWedge p (SourceDeRham.targetD π b) ω := by
  let e := RestrictScalars.addEquiv A B (⋀[B]^(p + 1) Omega)
  let ei := RestrictScalars.addEquiv A B (⋀[B]^p Omega)
  let _ : Module B (RestrictScalars A B (⋀[B]^p Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^p Omega)
  let _ : Module B (RestrictScalars A B (⋀[B]^(p + 1) Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^(p + 1) Omega)
  change e (dΩ p (ei.symm (b • ω))) = b • e (dΩ p (ei.symm ω)) +
    leftWedge p (SourceDeRham.targetD π b) ω
  classical
  have hmem : ω ∈ Submodule.span A
      (Set.range fun c : Fin (p + 1) → B =>
        c 0 • exteriorPower.ιMulti B p fun i => SourceDeRham.targetD π (c i.succ)) := by
    rw [targetFormGenerators_span π hπ p]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨c, rfl⟩ := hv
      let c' : Fin (p + 1) → B := Fin.cons (b * c 0) (fun i => c i.succ)
      have hmul : b • SourceDeRham.tgtGen π p c = SourceDeRham.tgtGen π p c' := by
        simp [SourceDeRham.tgtGen, c', mul_smul]
      have hmul' : ei.symm (b • SourceDeRham.tgtGen π p c) =
          ei.symm (SourceDeRham.tgtGen π p c') := by
        apply ei.injective
        exact hmul
      change e (dΩ p (ei.symm (b • SourceDeRham.tgtGen π p c))) =
        b • e (dΩ p (ei.symm (SourceDeRham.tgtGen π p c))) +
          leftWedge p (SourceDeRham.targetD π b) (SourceDeRham.tgtGen π p c)
      rw [hmul', show ei.symm (SourceDeRham.tgtGen π p c') =
        SourceDeRham.tgtGen π p c' from rfl,
        show ei.symm (SourceDeRham.tgtGen π p c) =
          SourceDeRham.tgtGen π p c from rfl]
      rw [hrule p c', hrule p c]
      change SourceDeRham.tgtGenRes π p c' =
        b • SourceDeRham.tgtGenRes π p c +
          leftWedge p (SourceDeRham.targetD π b) (SourceDeRham.tgtGen π p c)
      apply Subtype.ext
      simp only [SourceDeRham.tgtGenRes, SourceDeRham.tgtGen]
      rw [Submodule.coe_add, Submodule.coe_smul, leftWedge_coe]
      rw [coe_ιMulti_succ, coe_ιMulti_succ]
      simp only [c', Fin.cons_zero, Fin.cons_succ]
      simp only [SourceDeRham.targetD]
      have hd : π (KaehlerDifferential.D A B (b * c 0)) =
          b • π (KaehlerDifferential.D A B (c 0)) +
            c 0 • π (KaehlerDifferential.D A B b) := by
        rw [Derivation.leibniz]
        simp only [map_add, map_smul]
      rw [hd]
      simp only [map_add, map_smul]
      rw [Submodule.coe_smul]
      rw [Algebra.mul_smul_comm (c 0)
        (ExteriorAlgebra.ι B (π (KaehlerDifferential.D A B b))) _]
      simp only [add_mul, smul_mul_assoc]
  | zero => simp
  | add v w hv hw ihv ihw =>
      simp only [map_add, smul_add, ihv, ihw, add_assoc]
      abel
  | smul a v hv ih =>
      have hswap : b • (a • v) = algebraMap A B a • (b • v) := by
        rw [IsScalarTower.algebraMap_smul B a (b • v)]
        exact (smul_comm a b v).symm
      have hin : ei.symm (b • (a • v)) = a • ei.symm (b • v) := by
        rw [hswap, RestrictScalars.addEquiv_symm_map_algebraMap_smul]
      have hvsmul : ei.symm (a • v) = a • ei.symm v := by
        rw [show a • v = algebraMap A B a • v from (IsScalarTower.algebraMap_smul B a v).symm,
          RestrictScalars.addEquiv_symm_map_algebraMap_smul]
      rw [hin, map_smul, RestrictScalars.addEquiv_map_smul, ih]
      rw [hvsmul, smul_add, smul_smul]
      have hleft : leftWedge p (SourceDeRham.targetD π b) (a • v) =
          algebraMap A B a • leftWedge p (SourceDeRham.targetD π b) v := by
        rw [show a • v = algebraMap A B a • v from
          (IsScalarTower.algebraMap_smul B a v).symm, map_smul]
      rw [hleft, map_smul, RestrictScalars.addEquiv_map_smul, smul_smul,
        mul_comm (algebraMap A B a) b]

/-- The biadditive map `(m, ω) ↦ (∇ m) ∧ ω + m ⊗ dΩ ω` whose lift is the extension of a
connection to degree `p`. -/
public noncomputable def connectionFormPair
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (nabla : Connection A B π M) (p : ℕ) :
    M →+ (⋀[B]^p Omega →+ (M ⊗[B] (⋀[B]^(p + 1) Omega))) where
  toFun m := {
    toFun := fun ω =>
      TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla m) +
        m ⊗ₜ[B] descendedDifferential dΩ p ω
    map_zero' := by simp
    map_add' := by
      intro ω η
      simp [TensorProduct.map_add_right, TensorProduct.tmul_add]
      abel
  }
  map_zero' := by ext ω; simp
  map_add' := by
    intro m n
    ext ω
    change TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla (m + n)) +
        (m + n) ⊗ₜ[B] descendedDifferential dΩ p ω =
      (TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla m) +
          m ⊗ₜ[B] descendedDifferential dΩ p ω) +
        (TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla n) +
          n ⊗ₜ[B] descendedDifferential dΩ p ω)
    rw [nabla.map_add, TensorProduct.add_tmul]
    simp only [map_add]
    abel

/-- `connectionFormPair` is balanced over `B`: moving a scalar across the tensor sign is absorbed
by the Leibniz rules for the connection and for the descended differential. -/
public theorem connectionFormPair_balance
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ)
    (nabla : Connection A B π M) (p : ℕ)
    (m : M) (ω : ⋀[B]^p Omega) (b : B) :
    connectionFormPair π dΩ nabla p (b • m) ω =
      connectionFormPair π dΩ nabla p m (b • ω) := by
  let _ : Module A Omega := Module.compHom Omega (algebraMap A B)
  let _ : IsScalarTower A B Omega := ⟨fun a c x => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let _ : Module B (RestrictScalars A B (⋀[B]^p Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^p Omega)
  let _ : Module B (RestrictScalars A B (⋀[B]^(p + 1) Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^(p + 1) Omega)
  change TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla (b • m)) +
        (b • m) ⊗ₜ[B] descendedDifferential dΩ p ω =
      TensorProduct.map LinearMap.id ((leftWedge p).flip (b • ω)) (nabla m) +
        m ⊗ₜ[B] descendedDifferential dΩ p (b • ω)
  rw [nabla.leibniz]
  have hd := descendedDifferential_leibniz π dΩ hπ hrule p b ω
  simp only [map_add, map_smul, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [show TensorProduct.map LinearMap.id (b • (leftWedge p).flip ω) =
    b • TensorProduct.map LinearMap.id ((leftWedge p).flip ω) from
      TensorProduct.map_smul_right b LinearMap.id ((leftWedge p).flip ω),
    LinearMap.smul_apply]
  rw [hd]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [show ((leftWedge p).flip ω) (π (KaehlerDifferential.D A B b)) =
    leftWedge p (SourceDeRham.targetD π b) ω from rfl]
  abel

/-- `connectionFormPair` is homogeneous for scalars coming from the base ring `A`. -/
public theorem connectionFormPair_algebraMap_smul
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (nabla : Connection A B π M) (p : ℕ)
    (m : M) (ω : ⋀[B]^p Omega) (a : A) :
    connectionFormPair π dΩ nabla p m (algebraMap A B a • ω) =
      algebraMap A B a • connectionFormPair π dΩ nabla p m ω := by
  let _ : Module B (RestrictScalars A B (⋀[B]^p Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^p Omega)
  let _ : Module B (RestrictScalars A B (⋀[B]^(p + 1) Omega)) :=
    RestrictScalars.moduleOrig A B (⋀[B]^(p + 1) Omega)
  change TensorProduct.map LinearMap.id ((leftWedge p).flip (algebraMap A B a • ω))
        (nabla m) + m ⊗ₜ[B] descendedDifferential dΩ p (algebraMap A B a • ω) =
      algebraMap A B a •
        (TensorProduct.map LinearMap.id ((leftWedge p).flip ω) (nabla m) +
          m ⊗ₜ[B] descendedDifferential dΩ p ω)
  rw [show (leftWedge p).flip (algebraMap A B a • ω) =
      algebraMap A B a • (leftWedge p).flip ω from map_smul _ _ _,
    TensorProduct.map_smul_right, LinearMap.smul_apply]
  have hd : descendedDifferential dΩ p (algebraMap A B a • ω) =
      algebraMap A B a • descendedDifferential dΩ p ω := by
    change RestrictScalars.addEquiv A B _ (dΩ p ((RestrictScalars.addEquiv A B
        (⋀[B]^p Omega)).symm (algebraMap A B a • ω))) =
      algebraMap A B a • RestrictScalars.addEquiv A B _
        (dΩ p ((RestrictScalars.addEquiv A B (⋀[B]^p Omega)).symm ω))
    rw [RestrictScalars.addEquiv_symm_map_algebraMap_smul, map_smul,
      RestrictScalars.addEquiv_map_smul]
  rw [hd, TensorProduct.tmul_smul, ← smul_add]

/-- The extension of a connection to degree `p`, as an additive map. -/
public noncomputable def connectionFormAddMap
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ)
    (nabla : Connection A B π M) (p : ℕ) :
    M ⊗[B] (⋀[B]^p Omega) →+ M ⊗[B] (⋀[B]^(p + 1) Omega) :=
  TensorProduct.liftAddHom (connectionFormPair π dΩ nabla p)
    (by
      intro b m ω
      exact connectionFormPair_balance π dΩ hπ hrule nabla p m ω b)

private theorem connectionFormAddMap_tmul
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ)
    (nabla : Connection A B π M) (p : ℕ)
    (m : M) (ω : ⋀[B]^p Omega) :
    connectionFormAddMap π dΩ hπ hrule nabla p (m ⊗ₜ[B] ω) =
      connectionFormPair π dΩ nabla p m ω := rfl

private theorem connectionFormAddMap_algebraMap_smul
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ)
    (nabla : Connection A B π M) (p : ℕ)
    (a : A) (x : M ⊗[B] (⋀[B]^p Omega)) :
    connectionFormAddMap π dΩ hπ hrule nabla p (algebraMap A B a • x) =
      algebraMap A B a • connectionFormAddMap π dΩ hπ hrule nabla p x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy]
  | tmul m ω =>
      rw [TensorProduct.smul_tmul' (R := B) (R' := B) (algebraMap A B a) m ω]
      rw [TensorProduct.smul_tmul (R := B) (R' := B),
        connectionFormAddMap_tmul, connectionFormAddMap_tmul,
        connectionFormPair_algebraMap_smul]

/-- The extension of a connection to degree `p`, as an `A`-linear map between the
`RestrictScalars` synonyms. -/
public noncomputable def connectionFormLinearMap
    (π : Ω[B⁄A] →ₗ[B] Omega)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (hπ : Function.Surjective π) (hrule : SourceDeRham.SatisfiesRule π dΩ)
    (nabla : Connection A B π M) (p : ℕ) :
    RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
      RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) where
  toFun x := (RestrictScalars.addEquiv A B _).symm
    (connectionFormAddMap π dΩ hπ hrule nabla p (RestrictScalars.addEquiv A B _ x))
  map_add' x y := by simp [connectionFormAddMap]
  map_smul' a x := by
    apply (RestrictScalars.addEquiv A B _).injective
    simp only [RestrictScalars.addEquiv_map_smul]
    exact connectionFormAddMap_algebraMap_smul π dΩ hπ hrule nabla p a
      (RestrictScalars.addEquiv A B _ x)

/-- An extension of a connection to differential forms, in the setting of [Stacks, Tag 07HY]:
`π` is surjective and its kernel is generated by good generators, so the descended de Rham
differential is unique and squares to zero (`ExtendedConnection.deRhamDifferential_comp_self`).
The field `toLinearMap p` is the map from degree `p` to degree `p + 1`; `map_tmul` records its
defining formula. -/
public structure ExtendedConnection
    (S : SourceDeRham A B) (π : Ω[B⁄A] →ₗ[B] Omega)
    (nabla : Connection A B π M) where
  /-- The quotient map is surjective, as in [Stacks, Tag 07HY]. -/
  surjective : Function.Surjective π
  /-- The kernel of the quotient map is generated by good generators, as in [Stacks, Tag 07HY]. -/
  generation : S.GenerationHypothesis π
  /-- The de Rham differential descended to the exterior powers of `Omega`. -/
  deRhamDifferential : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1)
  /-- The descended differential makes the defining squares commute. -/
  commutes : S.Commutes π deRhamDifferential
  /-- The extension of the connection in every degree. -/
  toLinearMap : ∀ p, RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
    RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega))
  /-- The extended connection on a pure tensor. -/
  map_tmul : ∀ (p : ℕ) (m : M) (omega : ⋀[B]^p Omega),
    RestrictScalars.addEquiv A B _ (toLinearMap p (m ⊗ₜ[B] omega)) =
      TensorProduct.map LinearMap.id ((leftWedge p).flip omega) (nabla m) +
        m ⊗ₜ[B]
          RestrictScalars.addEquiv A B _ (deRhamDifferential p omega)

/-- A connection extends to the tensor products with all exterior powers of `Omega`. On a pure
tensor its value is the wedge of the connection term with the form, plus the coefficient tensored
with the descended de Rham differential of the form.

`S` is not de Rham data: `Stacks.DeRham.DifferentialDescent.sourceDeRham` constructs the de Rham
complex of `B` over `A` ([Stacks, Tag 0FKF]) and
`Stacks.DeRham.DifferentialDescent.SourceDeRham.eq_sourceDeRham` proves it is the only term of
`SourceDeRham A B`, so `S` names that complex; its square-zero property is derived from the
defining rule on generators by `Stacks.DeRham.DifferentialDescent.comp_eq_zero_of_gen`.  The
quotient `π : Ω[B⁄A] → Omega` with `hπ` and `hgen` is the setting [Stacks, Tag 07I0] itself
fixes, by reference to [Stacks, Tag 07HY]. -/
public noncomputable def extendedConnection
    (S : SourceDeRham A B) (π : Ω[B⁄A] →ₗ[B] Omega)
    (hπ : Function.Surjective π) (hgen : S.GenerationHypothesis π)
    (nabla : Connection A B π M) : ExtendedConnection S π nabla := by
  let dΩ := Classical.choose (exists_unique_quotient_deRhamDifferential S π hπ hgen)
  have hdΩ := Classical.choose_spec (exists_unique_quotient_deRhamDifferential S π hπ hgen)
  rcases hdΩ with ⟨hcomm, hrule, _⟩
  exact {
    surjective := hπ
    generation := hgen
    deRhamDifferential := dΩ
    commutes := hcomm
    toLinearMap := fun p => connectionFormLinearMap π dΩ hπ hrule nabla p
    map_tmul := by
      intro p m omega
      change connectionFormAddMap π dΩ hπ hrule nabla p (m ⊗ₜ[B] omega) = _
      rw [connectionFormAddMap_tmul]
      rfl
  }

/-- The descended de Rham differential of an extended connection squares to zero: by the
uniqueness in [Stacks, Tag 07HY] it is the quotient differential, which is a complex. -/
public theorem ExtendedConnection.deRhamDifferential_comp_self
    {S : SourceDeRham A B} {π : Ω[B⁄A] →ₗ[B] Omega} {nabla : Connection A B π M}
    (E : ExtendedConnection S π nabla) (p : ℕ) :
    (E.deRhamDifferential (p + 1)).comp (E.deRhamDifferential p) = 0 := by
  obtain ⟨dΩ, -, -, huniq, hsq⟩ :=
    exists_unique_quotient_deRhamDifferential S π E.surjective E.generation
  rw [huniq E.deRhamDifferential E.commutes]
  exact hsq p

end Extended

/-! ### Integrable connections -/

section Integrable

open scoped TensorProduct

namespace Connection

open Stacks.DeRham.DifferentialDescent

universe u v

variable {A B Omega : Type u} {M : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup M] [Module B M]

/-- A connection is integrable if its composite with its canonical extension from one-forms to
two-forms is zero.

As in `Crystalline.extendedConnection`, `S` is not de Rham data: it can only be
`Stacks.DeRham.DifferentialDescent.sourceDeRham A B`, the de Rham complex of [Stacks, Tag 0FKF],
by `Stacks.DeRham.DifferentialDescent.SourceDeRham.eq_sourceDeRham`. -/
public noncomputable def IsIntegrable
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) : Prop :=
  let extended := extendedConnection S pi hpi hgen nabla
  ∀ m : M,
    extended.toLinearMap 1
      (TensorProduct.map LinearMap.id
        (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)) = 0

/-- Integrability is equivalent to the vanishing of the displayed composite from the
connection to its canonical degree-one extension. -/
public theorem isIntegrable_iff_comp_eq_zero
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) :
    IsIntegrable S pi hpi hgen nabla ↔
      ∀ m : M,
        (extendedConnection S pi hpi hgen nabla).toLinearMap 1
          (TensorProduct.map LinearMap.id
            (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)) = 0 :=
  Iff.rfl

/-- The curvature composite of an integrable connection vanishes on every section. -/
public theorem IsIntegrable.comp_eq_zero
    {S : SourceDeRham A B} {pi : Ω[B⁄A] →ₗ[B] Omega}
    {hpi : Function.Surjective pi} {hgen : S.GenerationHypothesis pi}
    {nabla : Connection A B pi M}
    (h : IsIntegrable S pi hpi hgen nabla) (m : M) :
    (extendedConnection S pi hpi hgen nabla).toLinearMap 1
      (TensorProduct.map LinearMap.id
        (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)) = 0 :=
  (isIntegrable_iff_comp_eq_zero S pi hpi hgen nabla).mp h m

/-- A connection whose canonical curvature composite vanishes is integrable. -/
public theorem isIntegrable_of_comp_eq_zero
    {S : SourceDeRham A B} {pi : Ω[B⁄A] →ₗ[B] Omega}
    {hpi : Function.Surjective pi} {hgen : S.GenerationHypothesis pi}
    {nabla : Connection A B pi M}
    (h : ∀ m : M,
      (extendedConnection S pi hpi hgen nabla).toLinearMap 1
        (TensorProduct.map LinearMap.id
          (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)) = 0) :
    IsIntegrable S pi hpi hgen nabla :=
  (isIntegrable_iff_comp_eq_zero S pi hpi hgen nabla).mpr h

end Connection

end Integrable

end Crystalline

end

end MathlibExt.DeRhamSource

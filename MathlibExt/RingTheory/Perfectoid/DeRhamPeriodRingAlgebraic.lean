/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/G9/HenselEmb.lean`,
`ZInQKernel/Contrib/G9/BdREmb.lean` and `ZInQKernel/Contrib/G9/G9.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.HenselianLift
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingGalois

/-!
# The algebraic closure of `ℚ_p` inside `B_dR^+`

`B_dR^+ = BDeRhamPlus 𝓞_ℂ_[p] p` is a complete discrete valuation ring whose residue map is
Fontaine's map `θ : B_dR^+ → ℂ_[p]`, a surjective `ℚ_[p]`-algebra map. By Hensel's lemma, every
finite extension of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p` lifts uniquely through `θ`, and these lifts
glue to the unique `ℚ_[p]`-algebra map `ℚ̄_p → B_dR^+` whose composite with `θ` is the inclusion
`ℚ̄_p ⊆ ℂ_[p]` (`PadicComplexInt.padicAlgClToBDeRhamPlus`). By uniqueness it is equivariant for
the action of `Gal(ℚ̄_p/ℚ_p)` (`PadicComplexInt.galoisBDeRhamPlus_padicAlgClToBDeRhamPlus`).

Fontaine deduces that `B_dR^+` is a `ℚ̄_p`-algebra from its Galois invariants (J.-M. Fontaine,
*Le corps des périodes p-adiques*, Astérisque 223 (1994), Exposé II, §1.5.7 p. 74); here the
embedding is constructed directly by Hensel's lemma.
-/

@[expose] public noncomputable section

open Ideal WittVector MathlibExt.AlgebraicGeometry.HodgeTateComparison
open scoped IntermediateField

namespace PadicComplexInt

variable (p : ℕ) [hp : Fact p.Prime]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p

/-- `B_dR^+` is henselian along the kernel of `θ`. -/
instance henselianRing_ker_fontaineThetaBDeRhamPlus :
    HenselianRing 𝔹⁺ (RingHom.ker (fontaineThetaBDeRhamPlus p)) := by
  rw [ker_fontaineThetaBDeRhamPlus]
  infer_instance

/-- Every finite extension `K` of `ℚ_p` inside `ℚ̄_p` lifts through `θ`. -/
private theorem exists_comp_fontaineThetaBDeRhamPlus_eq
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ f : K →ₐ[ℚ_[p]] 𝔹⁺, (fontaineThetaBDeRhamPlus p).comp f =
      (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp K.val :=
  AlgHom.exists_comp_eq_of_henselianRing _ (fontaineThetaBDeRhamPlus_surjective p)
    (fun _ hy => isUnit_of_fontaineThetaBDeRhamPlus_ne_zero p hy) _

/-- The lift `K → B_dR^+` through `θ` of `K ⊆ ℚ̄_p ⊆ ℂ_[p]`, for a finite extension `K` of `ℚ_p`
inside `ℚ̄_p`. -/
private def liftFinite (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    K →ₐ[ℚ_[p]] 𝔹⁺ :=
  (exists_comp_fontaineThetaBDeRhamPlus_eq p K).choose

/-- `θ` maps the lift of `x ∈ K` to `x ∈ ℂ_[p]`. -/
private theorem fontaineThetaBDeRhamPlus_liftFinite (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (x : K) :
    fontaineThetaBDeRhamPlus p (liftFinite p K x) = ((x : PadicAlgCl p) : ℂ_[p]) :=
  DFunLike.congr_fun (exists_comp_fontaineThetaBDeRhamPlus_eq p K).choose_spec x

/-- The lifts of finite extensions are compatible with inclusions, by uniqueness of lifts. -/
private theorem liftFinite_inclusion {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] K'] (h : K ≤ K') (x : K) :
    liftFinite p K' (IntermediateField.inclusion h x) = liftFinite p K x := by
  have : (liftFinite p K').comp (IntermediateField.inclusion h) = liftFinite p K :=
    AlgHom.ext_of_comp_eq (fontaineThetaBDeRhamPlus p) (AlgHom.ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
        fontaineThetaBDeRhamPlus_liftFinite, fontaineThetaBDeRhamPlus_liftFinite]
      rfl)
  exact DFunLike.congr_fun this x

/-- The glued lift `ℚ̄_p → B_dR^+`, as a function: `x` is sent to its image under the lift of the
finite extension `ℚ_p⟮x⟯`. -/
private def gluedLiftFun (x : PadicAlgCl p) : 𝔹⁺ :=
  liftFinite p ℚ_[p]⟮x⟯ ⟨x, IntermediateField.mem_adjoin_simple_self ℚ_[p] x⟩

/-- The glued lift agrees with the lift of any finite extension `K` containing `x`. -/
private theorem gluedLiftFun_eq (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {x : PadicAlgCl p} (hx : x ∈ K) :
    gluedLiftFun p x = liftFinite p K ⟨x, hx⟩ :=
  (liftFinite_inclusion p (IntermediateField.adjoin_simple_le_iff.mpr hx) _).symm

/-- `x` and `y` lie in the finite extension `ℚ_p⟮x⟯ ⊔ ℚ_p⟮y⟯`. -/
private theorem mem_adjoin_sup_adjoin (x y : PadicAlgCl p) :
    x ∈ ℚ_[p]⟮x⟯ ⊔ ℚ_[p]⟮y⟯ ∧ y ∈ ℚ_[p]⟮x⟯ ⊔ ℚ_[p]⟮y⟯ :=
  ⟨le_sup_left (b := ℚ_[p]⟮y⟯) (IntermediateField.mem_adjoin_simple_self ℚ_[p] x),
    le_sup_right (a := ℚ_[p]⟮x⟯) (IntermediateField.mem_adjoin_simple_self ℚ_[p] y)⟩

/-- The glued lift `ℚ̄_p → B_dR^+` of the finite extensions of `ℚ_p` inside `ℚ̄_p`. -/
private def gluedLift : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹⁺ where
  toFun := gluedLiftFun p
  map_one' := by
    rw [gluedLiftFun_eq p ⊥ (one_mem _)]
    exact map_one (liftFinite p ⊥)
  map_mul' x y := by
    obtain ⟨hx, hy⟩ := mem_adjoin_sup_adjoin p x y
    rw [gluedLiftFun_eq p _ (mul_mem hx hy), gluedLiftFun_eq p _ hx,
      gluedLiftFun_eq p _ hy, ← map_mul]
    rfl
  map_zero' := by
    rw [gluedLiftFun_eq p ⊥ (zero_mem _)]
    exact map_zero (liftFinite p ⊥)
  map_add' x y := by
    obtain ⟨hx, hy⟩ := mem_adjoin_sup_adjoin p x y
    rw [gluedLiftFun_eq p _ (add_mem hx hy), gluedLiftFun_eq p _ hx,
      gluedLiftFun_eq p _ hy, ← map_add]
    rfl
  commutes' r := by
    rw [gluedLiftFun_eq p ⊥ (algebraMap_mem _ r)]
    exact (liftFinite p ⊥).commutes r

/-- The composite of the glued lift with `θ` is the inclusion `ℚ̄_p ⊆ ℂ_[p]`. -/
private theorem comp_gluedLift :
    (fontaineThetaBDeRhamPlus p).comp (gluedLift p) =
      IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p] :=
  AlgHom.ext fun _ => fontaineThetaBDeRhamPlus_liftFinite p _ _

/-- Two `ℚ_[p]`-algebra maps `ℚ̄_p → B_dR^+` with the same composite with `θ` are equal: their
restrictions to each finite extension `ℚ_p⟮x⟯` are equal by uniqueness of lifts. -/
private theorem eq_of_comp_eq {f g : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹⁺}
    (h : (fontaineThetaBDeRhamPlus p).comp f = (fontaineThetaBDeRhamPlus p).comp g) :
    f = g := by
  ext x
  have hfg : f.comp ℚ_[p]⟮x⟯.val = g.comp ℚ_[p]⟮x⟯.val :=
    AlgHom.ext_of_comp_eq (fontaineThetaBDeRhamPlus p) (by
      rw [← AlgHom.comp_assoc, h, AlgHom.comp_assoc])
  exact DFunLike.congr_fun hfg ⟨x, IntermediateField.mem_adjoin_simple_self ℚ_[p] x⟩

/-- There is a unique `ℚ_[p]`-algebra map `ℚ̄_p → B_dR^+` whose composite with Fontaine's map
`θ : B_dR^+ → ℂ_[p]` is the inclusion `ℚ̄_p ⊆ ℂ_[p]`. -/
theorem existsUnique_comp_fontaineThetaBDeRhamPlus :
    ∃! f : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹⁺,
      (fontaineThetaBDeRhamPlus p).comp f = IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p] :=
  ⟨gluedLift p, comp_gluedLift p,
    fun _ hg => eq_of_comp_eq p (hg.trans (comp_gluedLift p).symm)⟩

/-- **The embedding `ℚ̄_p → B_dR^+`**: the unique `ℚ_[p]`-algebra map whose composite with
Fontaine's map `θ : B_dR^+ → ℂ_[p]` is the inclusion `ℚ̄_p ⊆ ℂ_[p]`. -/
def padicAlgClToBDeRhamPlus : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹⁺ :=
  (existsUnique_comp_fontaineThetaBDeRhamPlus p).exists.choose

/-- `θ` maps the image of `x ∈ ℚ̄_p` in `B_dR^+` to `x ∈ ℂ_[p]`. -/
@[simp]
theorem fontaineThetaBDeRhamPlus_padicAlgClToBDeRhamPlus (x : PadicAlgCl p) :
    fontaineThetaBDeRhamPlus p (padicAlgClToBDeRhamPlus p x) = (x : ℂ_[p]) :=
  DFunLike.congr_fun (existsUnique_comp_fontaineThetaBDeRhamPlus p).exists.choose_spec x

/-- A `ℚ_[p]`-algebra map `ℚ̄_p → B_dR^+` whose composite with `θ` is the inclusion
`ℚ̄_p ⊆ ℂ_[p]` is `padicAlgClToBDeRhamPlus p`. -/
theorem eq_padicAlgClToBDeRhamPlus {f : PadicAlgCl p →ₐ[ℚ_[p]] 𝔹⁺}
    (hf : (fontaineThetaBDeRhamPlus p).comp f =
      IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]) :
    f = padicAlgClToBDeRhamPlus p :=
  (existsUnique_comp_fontaineThetaBDeRhamPlus p).unique hf
    (existsUnique_comp_fontaineThetaBDeRhamPlus p).exists.choose_spec

/-- The map `ℚ̄_p → B_dR^+` is injective. -/
theorem padicAlgClToBDeRhamPlus_injective :
    Function.Injective (padicAlgClToBDeRhamPlus p) :=
  (padicAlgClToBDeRhamPlus p).toRingHom.injective

/-- **Galois equivariance of `ℚ̄_p ⊆ B_dR^+`**: `σ (ι x) = ι (σ x)` for `σ ∈ Gal(ℚ̄_p/ℚ_p)`. -/
theorem galoisBDeRhamPlus_padicAlgClToBDeRhamPlus (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (x : PadicAlgCl p) :
    galoisBDeRhamPlus p σ (padicAlgClToBDeRhamPlus p x) = padicAlgClToBDeRhamPlus p (σ x) := by
  have : (galoisBDeRhamPlus p σ).comp (padicAlgClToBDeRhamPlus p) =
      (padicAlgClToBDeRhamPlus p).comp σ.toAlgHom :=
    eq_of_comp_eq p (AlgHom.ext fun y => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
        fontaineThetaBDeRhamPlus_galoisBDeRhamPlus,
        fontaineThetaBDeRhamPlus_padicAlgClToBDeRhamPlus,
        fontaineThetaBDeRhamPlus_padicAlgClToBDeRhamPlus]
      exact completionGalois_coe p σ y)
  exact DFunLike.congr_fun this x

end PadicComplexInt

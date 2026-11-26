/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Functor.RelativeProjectivityTransport
public import MathlibExt.Algebra.Category.ModuleCat.RingHomInduction.Composition
public import MathlibExt.Algebra.Category.ModuleCat.CoextendScalarsRelativeInjectivity

/-!
# Relative projectivity and injectivity under scalar transport

For ring homomorphisms `k → R → S`, direct restriction along the
composite and successive restriction give the same relative lifting
and extension properties. Relative projectivity or injectivity for
restriction to `k` implies the corresponding property for restriction
to `R`. The induction counit then splits, or the coextension unit
retracts. Direct and iterated induction, coextension, and their retracts
supply these intermediate relative properties. All rings may be
noncommutative, with independent ring and module carrier universes.
-/

@[expose] public section

open CategoryTheory

universe u v s w

namespace ModuleCat.RelativeScalarTransport

variable {k : Type u} {R : Type v} {S : Type s}
  [Ring k] [Ring R] [Ring S]

/-- Let `k,R,S` be rings in independent universes `u,v,s`,
`φ : k → R`, `ψ : R → S` ring homomorphisms, and `P` an `S`-module
with carrier in `w`. Relative projectivity for restriction along `ψφ` is equivalent
to relative projectivity for restriction first along `ψ`, then along
`φ`, as lifting properties against maps split after that restriction. -/
theorem isRelativeProjective_restrict_comp_iff (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{w} S) :
    (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeProjective P ↔
      ((ModuleCat.restrictScalars.{w} ψ) ⋙
        (ModuleCat.restrictScalars.{w} φ)).IsRelativeProjective P :=
  Functor.isRelativeProjective_iff_of_natIso (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl) P

/-- Let `k,R,S` be rings in independent universes `u,v,s`,
`φ : k → R`, `ψ : R → S` ring homomorphisms, and `P` an `S`-module
with carrier in `w`. Relative injectivity for restriction along `ψφ` is equivalent
to relative injectivity for restriction first along `ψ`, then along
`φ`, as extension properties against maps split after restriction. -/
theorem isRelativeInjective_restrict_comp_iff (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{w} S) :
    (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeInjective P ↔
      ((ModuleCat.restrictScalars.{w} ψ) ⋙
        (ModuleCat.restrictScalars.{w} φ)).IsRelativeInjective P :=
  Functor.isRelativeInjective_iff_of_natIso (ModuleCat.restrictScalarsComp' φ ψ (ψ.comp φ) rfl) P

/-- Let `k,R,S` be rings in independent universes `u,v,s`,
`φ : k → R`, `ψ : R → S` ring homomorphisms, and `P` an `S`-module
with carrier in `w`. If `P` is projective relative to restriction from `S` to `k`,
it is projective relative to restriction from `S` to `R`, since every
`R`-split epimorphism is also `k`-split. -/
theorem isRelativeProjective_restrict_of_comp (φ : k →+* R) (ψ : R →+* S)
    {P : ModuleCat.{w} S}
    (hP : (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeProjective P) :
    (ModuleCat.restrictScalars.{w} ψ).IsRelativeProjective P :=
  Functor.IsRelativeProjective.of_comp (ModuleCat.restrictScalars.{w} φ)
    ((isRelativeProjective_restrict_comp_iff φ ψ P).mp hP)

/-- Let `k,R,S` be rings in independent universes `u,v,s`,
`φ : k → R`, `ψ : R → S` ring homomorphisms, and `P` an `S`-module
with carrier in `w`. If `P` is injective relative to restriction from `S` to `k`,
it is injective relative to restriction from `S` to `R`, since every
`R`-split monomorphism is also `k`-split. -/
theorem isRelativeInjective_restrict_of_comp (φ : k →+* R) (ψ : R →+* S)
    {P : ModuleCat.{w} S}
    (hP : (ModuleCat.restrictScalars.{w} (ψ.comp φ)).IsRelativeInjective P) :
    (ModuleCat.restrictScalars.{w} ψ).IsRelativeInjective P :=
  Functor.IsRelativeInjective.of_comp (ModuleCat.restrictScalars.{w} φ)
    ((isRelativeInjective_restrict_comp_iff φ ψ P).mp hP)

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. For `P : ModuleCat_T(S)` projective relative to restriction
along `ψφ`, the induction–restriction counit along `ψ`,
`S ⊗[R] P → P`, is a split epimorphism. -/
theorem counit_isSplitEpi_of_relativeProjective_comp (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{max u v s w} S)
    (hP : (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)).IsRelativeProjective P) :
    IsSplitEpi ((ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s w} ψ).counit.app P) :=
  ((ModuleCat.induceRestrictScalarsAdj.{v, s, max u v s w} ψ).isRelativeProjective_iff_counit_isSplitEpi P).mp
    (isRelativeProjective_restrict_of_comp φ ψ hP)

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. For `P : ModuleCat_T(S)` injective relative to restriction
along `ψφ`, the restriction–coextension unit along `ψ` is a split
monomorphism. -/
theorem unit_isSplitMono_of_relativeInjective_comp (φ : k →+* R) (ψ : R →+* S)
    (P : ModuleCat.{max u v s w} S)
    (hP : (ModuleCat.restrictScalars.{max u v s w} (ψ.comp φ)).IsRelativeInjective P) :
    IsSplitMono ((ModuleCat.restrictCoextendScalarsAdj.{max u v s w} ψ).unit.app P) :=
  (ModuleCat.CoextendScalars.isRelativeInjective_iff_unit_isSplitMono.{v, s, max u v s w} ψ P).mp
    (isRelativeInjective_restrict_of_comp φ ψ hP)

/-- Let `k,R` be rings, `φ,φ′ : k → R` equal ring homomorphisms,
and `P` an `R`-module. Relative projectivity of `P` for restriction
along `φ` is equivalent to that for `φ′`. -/
theorem isRelativeProjective_restrict_congr {φ φ' : k →+* R} (h : φ = φ')
    (P : ModuleCat.{w} R) :
    (ModuleCat.restrictScalars.{w} φ).IsRelativeProjective P ↔
      (ModuleCat.restrictScalars.{w} φ').IsRelativeProjective P :=
  Functor.isRelativeProjective_iff_of_natIso (ModuleCat.restrictScalarsCongr h) P

/-- Let `k,R` be rings, `φ,φ′ : k → R` equal ring homomorphisms,
and `P` an `R`-module. Relative injectivity of `P` for restriction
along `φ` is equivalent to that for `φ′`. -/
theorem isRelativeInjective_restrict_congr {φ φ' : k →+* R} (h : φ = φ')
    (P : ModuleCat.{w} R) :
    (ModuleCat.restrictScalars.{w} φ).IsRelativeInjective P ↔
      (ModuleCat.restrictScalars.{w} φ').IsRelativeInjective P :=
  Functor.isRelativeInjective_iff_of_natIso (ModuleCat.restrictScalarsCongr h) P

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. For arbitrary `M : ModuleCat_T(k)`, the directly induced
module `S ⊗[k] M` is projective relative to restriction along `ψ`. -/
theorem isRelativeProjective_induced_comp (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective
      ((ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M) :=
  isRelativeProjective_restrict_of_comp φ ψ
    ((ModuleCat.induceRestrictScalarsAdj.{u, s, max u v s w} (ψ.comp φ)).isRelativeProjective_obj M)

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. For arbitrary `M : ModuleCat_T(k)`, the iterated induced
module `S ⊗[R] (R ⊗[k] M)` is projective relative to restriction
along `ψ`. -/
theorem isRelativeProjective_iterated_induced (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective
      (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
        (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M) := by
  intro Y Z g s f
  let e : (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M) ≅
      (ModuleCat.induceScalars.{u, s, max u v s w} (ψ.comp φ)).obj M :=
    (ModuleCat.RingHomInduction.compositionIso.{u, v, s, w} φ ψ).app M
  exact Functor.IsRelativeProjective.of_retract (isRelativeProjective_induced_comp φ ψ M)
    e.retract g s f

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. Every `S`-module retract of `S ⊗[R] (R ⊗[k] M)` for
`M : ModuleCat_T(k)` is projective relative to restriction along `ψ`. -/
theorem isRelativeProjective_retract_iterated_induced (φ : k →+* R) (ψ : R →+* S)
    (M : ModuleCat.{max u v s w} k) (P : ModuleCat.{max u v s w} S)
    (r : Retract P (((ModuleCat.induceScalars.{u, v, max u v s w} φ) ⋙
      (ModuleCat.induceScalars.{v, s, max u v s w} ψ)).obj M)) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeProjective P := by
  intro Y Z g s f
  exact Functor.IsRelativeProjective.of_retract
    (isRelativeProjective_iterated_induced φ ψ M) r g s f

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. For arbitrary `N : ModuleCat_T(k)`, coextension along `ψφ`
gives an `S`-module injective relative to restriction along `ψ`. -/
theorem isRelativeInjective_coextended_comp (φ : k →+* R) (ψ : R →+* S)
    (N : ModuleCat.{max u v s w} k) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeInjective
      ((ModuleCat.coextendScalars.{u, s, max u v s w} (ψ.comp φ)).obj N) :=
  isRelativeInjective_restrict_of_comp φ ψ
    (ModuleCat.CoextendScalars.isRelativeInjective_obj.{u, s, max u v s w} (ψ.comp φ) N)

/-- Let `k,R,S` be rings in universes `u,v,s` and
`φ : k → R`, `ψ : R → S` ring homomorphisms. Work with module
carriers at the common height `T=max(u,v,s,w)`. Every `S`-module retract of the coextension along `ψφ` of
`N : ModuleCat_T(k)` is injective relative to restriction along `ψ`. -/
theorem isRelativeInjective_retract_coextended_comp (φ : k →+* R) (ψ : R →+* S)
    (N : ModuleCat.{max u v s w} k) (P : ModuleCat.{max u v s w} S)
    (r : Retract P ((ModuleCat.coextendScalars.{u, s, max u v s w} (ψ.comp φ)).obj N)) :
    (ModuleCat.restrictScalars.{max u v s w} ψ).IsRelativeInjective P := by
  intro X Y g s f
  exact Functor.IsRelativeInjective.of_retract
    (isRelativeInjective_coextended_comp φ ψ N) r g s f

end ModuleCat.RelativeScalarTransport

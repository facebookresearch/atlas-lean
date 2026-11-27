/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.SemilocalCoinduced

@[expose] public section

open IsDedekindDomain NumberField

/-! ### The actions are scoped

Before the scopes are opened, neither the Galois action on finite places nor the
decomposition group actions on completions are instances. -/

section Unscoped

variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K]

example : True := by
  fail_if_success
    have : MulAction (K ≃ₐ[E] K) (HeightOneSpectrum (𝓞 K)) := inferInstance
  trivial

example (_w : HeightOneSpectrum (𝓞 K)) : True := by
  fail_if_success
    have : MulSemiringAction (PlaceDecomp.decomp E K _w) (_w.adicCompletion K) := inferInstance
  trivial

example (_w : InfinitePlace K) : True := by
  fail_if_success
    have : MulSemiringAction (InfPlaceDecomp.decomp E K _w) _w.Completion := inferInstance
  trivial

end Unscoped

/-! ### Finite places -/

section Finite

open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

variable {E K : Type*} [Field E] [Field K] [NumberField K] [Algebra E K]

/-! Opening `NumberField.PlaceTransport` and `NumberField.PlaceDecomp` provides the Galois
action on places and the decomposition group actions on the completion, its integers and their
units. -/

noncomputable example : MulAction (K ≃ₐ[E] K) (HeightOneSpectrum (𝓞 K)) := inferInstance

noncomputable example (w : HeightOneSpectrum (𝓞 K)) :
    MulSemiringAction (PlaceDecomp.decomp E K w) (w.adicCompletion K) := inferInstance

noncomputable example (w : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ := inferInstance

noncomputable example (w : HeightOneSpectrum (𝓞 K)) :
    MulSemiringAction (PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K) := inferInstance

noncomputable example (w : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (PlaceDecomp.decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  inferInstance

example (w : HeightOneSpectrum (𝓞 K)) :
    UniformContinuousConstSMul (PlaceDecomp.decomp E K w) (WithVal (w.valuation K)) :=
  inferInstance

/-- The place action moves primes by `σ`: `σ • w` is the prime `σ(w)`, so `σ` maps `w` into
`σ • w`, and `x ∈ σ • w` exactly when `σ⁻¹ • x ∈ w`. -/
example (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ∈ w.asIdeal) :
    σ • x ∈ (σ • w).asIdeal :=
  (PlaceTransport.smul_mem_smul_asIdeal_iff σ w x).2 hx

example (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (σ • w).asIdeal ↔ σ⁻¹ • x ∈ w.asIdeal :=
  PlaceTransport.mem_smul_asIdeal_iff σ w x

example (σ τ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) : (σ * τ) • w = σ • τ • w :=
  mul_smul σ τ w

/-- The Galois action carries a uniformizer at `w` to a uniformizer at `σ • w`. -/
example (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (π : K)
    (hπ : w.valuation K π = WithZero.exp (-1)) :
    (σ • w).valuation K (σ π) = WithZero.exp (-1) := by
  rw [PlaceTransport.valuation_apply_of_smul_eq rfl, hπ]

/-- On the image of `K`, an element of the decomposition group acts on the completion as
itself. -/
example (w : HeightOneSpectrum (𝓞 K)) (σ : PlaceDecomp.decomp E K w) (x : K) :
    σ • (x : w.adicCompletion K) = ((σ : K ≃ₐ[E] K) x : w.adicCompletion K) := by
  rw [PlaceDecomp.smul_def]
  exact PlaceDecomp.actRingEquiv_coe σ (WithVal.toVal _ x)

/-- The decomposition group action is a group action by ring automorphisms: identity and
products act as expected, and so do the induced actions on units. -/
example (w : HeightOneSpectrum (𝓞 K)) (x : w.adicCompletion K) :
    PlaceDecomp.actRingEquiv (1 : PlaceDecomp.decomp E K w) x = x := by
  rw [PlaceDecomp.actRingEquiv_one, RingEquiv.refl_apply]

example (w : HeightOneSpectrum (𝓞 K)) (σ τ : PlaceDecomp.decomp E K w)
    (x : w.adicCompletion K) :
    PlaceDecomp.actHom (σ * τ) x = PlaceDecomp.actHom σ (PlaceDecomp.actHom τ x) := by
  rw [map_mul]
  rfl

example (w : HeightOneSpectrum (𝓞 K)) (σ : PlaceDecomp.decomp E K w) (x y : w.adicCompletion K) :
    σ • (x * y) = σ • x * σ • y :=
  smul_mul' σ x y

example (w : HeightOneSpectrum (𝓞 K)) (σ τ : PlaceDecomp.decomp E K w)
    (u : (w.adicCompletion K)ˣ) :
    (((σ * τ) • u : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
      σ • τ • (u : w.adicCompletion K) := by
  rw [Units.coe_smul, mul_smul]

/-- The decomposition group action preserves the valuation, hence the integers, and on integer
units it is the action on the completion. -/
example (w : HeightOneSpectrum (𝓞 K)) (σ : PlaceDecomp.decomp E K w) (x : w.adicCompletion K) :
    Valued.v (σ • x) = Valued.v x :=
  PlaceDecomp.valued_actRingEquiv σ x

example (w : HeightOneSpectrum (𝓞 K)) (σ : PlaceDecomp.decomp E K w)
    (u : (w.adicCompletionIntegers K)ˣ) :
    (((σ • u : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) :
      w.adicCompletion K) = σ • ((u : w.adicCompletionIntegers K) : w.adicCompletion K) :=
  rfl

/-- The transport along `σ` is `σ` on the image of `K`. -/
example (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : K) :
    PlaceTransport.transport σ h (x : w.adicCompletion K) = (σ x : w'.adicCompletion K) :=
  PlaceTransport.transport_coe σ h (WithVal.toVal _ x)

/-- The transport is the unique continuous ring homomorphism between the completions that is
`σ` on the image of `K`. -/
example (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (f : w.adicCompletion K →+* w'.adicCompletion K) (hf : Continuous f)
    (hfK : ∀ x : K, f x = (σ x : w'.adicCompletion K)) :
    f = (PlaceTransport.transport σ h : w.adicCompletion K →+* w'.adicCompletion K) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  refine congrFun (UniformSpace.Completion.ext
    (f := fun y => f (HeightOneSpectrum.adicCompletion.ofCompletion y))
    (g := fun y => PlaceTransport.transport σ h (HeightOneSpectrum.adicCompletion.ofCompletion y))
    (hf.comp (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w))
    ((PlaceTransport.continuous_transport σ h).comp
      (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_) y
  rw [PlaceTransport.transport_coe]
  exact hfK a.ofVal

/-- The transport preserves valuations and integers, and its restriction to integers and to
units is the transport itself. -/
example (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (x : w.adicCompletion K) :
    Valued.v (PlaceTransport.transport σ h x) = Valued.v x :=
  PlaceTransport.valued_transport σ h x

example (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (x : w.adicCompletionIntegers K) :
    ((PlaceTransport.transportIntegers σ h x : w'.adicCompletionIntegers K) :
      w'.adicCompletion K) = PlaceTransport.transport σ h (x : w.adicCompletion K) :=
  PlaceTransport.coe_transportIntegers σ h x

example (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (u : (w.adicCompletion K)ˣ) :
    ((PlaceTransport.transportUnits σ h u : (w'.adicCompletion K)ˣ) : w'.adicCompletion K) =
      PlaceTransport.transport σ h (u : w.adicCompletion K) :=
  rfl

/-- When `σ` fixes `w`, the transport along `σ` is the decomposition group action. -/
example (w : HeightOneSpectrum (𝓞 K)) (σ : PlaceDecomp.decomp E K w)
    (h : (σ : K ≃ₐ[E] K) • w = w) :
    PlaceTransport.transport (σ : K ≃ₐ[E] K) h = PlaceDecomp.actRingEquiv σ :=
  rfl

end Finite

section FiniteSIdele

open scoped NumberField.PlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

/-- The chosen place lies over `v`. -/
example (v : HeightOneSpectrum (𝓞 E)) :
    (PlaceAbove.above E K v).asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal :=
  PlaceAbove.comap_above E K v

/-- The representation on local units is the decomposition group action, written
additively. -/
example (v : HeightOneSpectrum (𝓞 E)) (d : FiniteSIdele.D E K v)
    (u : ((PlaceAbove.above E K v).adicCompletion K)ˣ) :
    Additive.toMul ((FiniteSIdele.localUnits E K v).ρ d (Additive.ofMul u)) = d • u :=
  rfl

/-- The comparison map from integer units to units is the inclusion. -/
example (v : HeightOneSpectrum (𝓞 E))
    (u : ((PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    ((Additive.toMul ((FiniteSIdele.integerUnitsToUnits E K v).hom (Additive.ofMul u)) :
      ((PlaceAbove.above E K v).adicCompletion K)ˣ) : (PlaceAbove.above E K v).adicCompletion K) =
      ((u : (PlaceAbove.above E K v).adicCompletionIntegers K) :
        (PlaceAbove.above E K v).adicCompletion K) :=
  rfl

end FiniteSIdele

/-! ### Infinite places -/

section Infinite

open scoped NumberField.InfPlaceDecomp

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

noncomputable example (w : InfinitePlace K) :
    MulSemiringAction (InfPlaceDecomp.decomp E K w) w.Completion := inferInstance

noncomputable example (w : InfinitePlace K) :
    MulDistribMulAction (InfPlaceDecomp.decomp E K w) w.Completionˣ := inferInstance

example (w : InfinitePlace K) :
    ContinuousConstSMul (InfPlaceDecomp.decomp E K w) w.Completion := inferInstance

/-- On the image of `K`, an element of the decomposition group of an infinite place acts on the
completion as itself. -/
example (w : InfinitePlace K) (σ : InfPlaceDecomp.decomp E K w) (x : K) :
    σ • (x : w.Completion) = ((σ : K ≃ₐ[E] K) x : w.Completion) := by
  rw [InfPlaceDecomp.smul_def]
  exact InfPlaceDecomp.actRingEquiv_coe σ (WithAbs.toAbs _ x)

example (w : InfinitePlace K) (σ τ : InfPlaceDecomp.decomp E K w) (x : w.Completion) :
    InfPlaceDecomp.actHom (σ * τ) x = InfPlaceDecomp.actHom σ (InfPlaceDecomp.actHom τ x) := by
  rw [map_mul]
  rfl

example (w : InfinitePlace K) (x : w.Completion) :
    InfPlaceDecomp.actRingEquiv (1 : InfPlaceDecomp.decomp E K w) x = x := by
  rw [InfPlaceDecomp.actRingEquiv_one, RingEquiv.refl_apply]

/-- The transport along `σ` between archimedean completions is `σ` on the image of `K`. -/
example (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : K) :
    InfinitePlaceTransport.transport σ h (x : w.Completion) = (σ x : w'.Completion) :=
  InfinitePlaceTransport.transport_coe σ h (WithAbs.toAbs _ x)

/-- The transport is the unique continuous ring homomorphism between the archimedean
completions that is `σ` on the image of `K`. -/
example (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w')
    (f : w.Completion →+* w'.Completion) (hf : Continuous f)
    (hfK : ∀ x : K, f x = (σ x : w'.Completion)) :
    f = (InfinitePlaceTransport.transport σ h : w.Completion →+* w'.Completion) := by
  refine RingHom.ext fun x => ?_
  refine congrFun (AbsoluteValue.Completion.ext hf
    (InfinitePlaceTransport.continuous_transport σ h) fun a => ?_) x
  rw [InfinitePlaceTransport.transport_coe]
  exact hfK a.ofAbs

/-- The places `w` and `σ • w` take the same values on `x` and `σ x`. -/
example (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (x : K) : w' (σ x) = w x :=
  InfinitePlaceTransport.apply_apply_of_smul_eq h x

/-- When `σ` fixes an infinite place `w`, the transport along `σ` is the decomposition group
action. -/
example (w : InfinitePlace K) (σ : InfPlaceDecomp.decomp E K w)
    (h : (σ : K ≃ₐ[E] K) • w = w) :
    InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = InfPlaceDecomp.actRingEquiv σ :=
  rfl

example (σ : K ≃ₐ[E] K) {w w' : InfinitePlace K} (h : σ • w = w') (u : w.Completionˣ) :
    ((InfinitePlaceTransport.transportUnits σ h u : w'.Completionˣ) : w'.Completion) =
      InfinitePlaceTransport.transport σ h (u : w.Completion) :=
  Units.coe_mapEquiv _ u

end Infinite

section ArchIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

/-- The chosen infinite place restricts to `v`. -/
example (v : InfinitePlace E) : (ArchIdele.above E K v).comap (algebraMap E K) = v :=
  ArchIdele.comap_above E K v

end ArchIdele

/-! ### The semilocal equivalences -/

open scoped NumberField.PlaceTransport

-- Consumer with the original binders for the finite place variant.
example (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : HeightOneSpectrum (𝓞 E)) :
    ∃ e : (Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v))
          ≃+ Additive (Π w : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v},
            (w.1.adicCompletion K)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v))
        (w w' : {w : HeightOneSpectrum (𝓞 K) // w.under (𝓞 E) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.FiniteSIdele.D E K v).subtype
          (NumberField.FiniteSIdele.localUnits E K v)).ρ g f)) w
          = NumberField.PlaceTransport.transportUnits g h (Additive.toMul (e f) w') :=
  NumberField.FiniteSIdele.exists_addEquiv_coind_localUnits E K v

-- Consumer with the original binders for the archimedean variant.
example (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
          ≃+ Additive (Π w : {w : NumberField.InfinitePlace K //
            w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (g : K ≃ₐ[E] K)
        (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (w w' : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v})
        (h : g • w'.1 = w.1),
        Additive.toMul (e ((Rep.coind (NumberField.InfPlaceDecomp.decomp E K
          (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K
            (NumberField.ArchIdele.above E K v))).ρ g f)) w
          = NumberField.InfinitePlaceTransport.transportUnits g h
            (Additive.toMul (e f) w') :=
  NumberField.ArchIdele.exists_addEquiv_coind_localUnits E K v

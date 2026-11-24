/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Algebra/Homology/HomologicalComplex/Basic.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Additional API for homological complexes

This file records additivity of the cycles functor, degreewise recursion for powers of a
complex endomorphism, and the existence of coproducts of complexes, computed degreewise. It also
records the basic properties of the maps
`K.toCycles i j : K.X i ⟶ K.cycles j` induced by the differentials: they kill the cycles in degree
`i`, commute with morphisms of complexes, vanish after a morphism from a complex concentrated in
degree `i`, and are epimorphisms in degrees where the complex is exact; consequently, a morphism of
complexes which is an epimorphism in degree `i` induces an epimorphism on cycles in degree `j` when
its target is exact at `j` (`HomologicalComplex.epi_cyclesMap_of_exactAt`). In a degree with no
nonzero differential into it, the identification of the homology with the cycles is natural
(`HomologicalComplex.isoHomologyπ_inv_naturality`). The sequence
`Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of cycles is exact when `j = c.next i`
(`HomologicalComplex.cyclesShortComplex_exact`). For adjacent degrees `i` and `j`, the cycles of a
complex exact in degree `j` fit into a short exact sequence `0 ⟶ Zᵢ ⟶ Kᵢ ⟶ Zⱼ ⟶ 0`
(`HomologicalComplex.cyclesShortComplex_shortExact`, written out as
`HomologicalComplex.shortExact_mk_iCycles_toCycles`), which stays short exact when its outer terms
are replaced by isomorphic objects
(`HomologicalComplex.cyclesShortComplex_shortExact_of_iso`), and whose second map `Kᵢ ⟶ Zⱼ` is an
isomorphism when `Zᵢ` vanishes (`HomologicalComplex.isIso_toCycles_of_isZero_cycles`); in
particular `K⁰ ⟶ Z¹` is an isomorphism for a cochain complex exact in degrees `0` and `1`
(`CochainComplex.isIso_toCycles_zero_of_exactAt`). A monomorphism of nonnegative cochain
complexes that is an isomorphism on zero cochains induces an isomorphism on zero cohomology
(`CochainComplex.isIso_homologyMap_zero_of_mono`). Likewise a
monomorphism onto the kernel of the differential `Kᵢ ⟶ Kⱼ` gives a short exact sequence
`0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` (`HomologicalComplex.shortExact_toCycles`). A morphism of complexes
vanishing in some degree induces zero on homology there
(`HomologicalComplex.homologyMap_eq_zero_of_f_eq_zero`), and two morphisms of complexes agreeing on
the cycles in some degree induce the same map on homology there
(`HomologicalComplex.homologyMap_eq_of_iCycles_comp`). Constructing the bundled cycle
sequence requires homology only in the two selected degrees.
The exactness results additionally require homology of the cycle sequence itself.
In an abelian category, the map from the opcycles in degree `i` to the cycles in degree `j` is an
isomorphism when the complex is exact in both degrees (`HomologicalComplex.isIso_opcyclesToCycles`).
For chain complexes indexed by the natural numbers, the identification of zero chains with
cycles is natural (`ChainComplex.cycles₀Iso_inv_naturality`), and so is the passage from zero
chains to zeroth homology (`ChainComplex.pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap`).
The isomorphisms `homologyIsoSc'`
are natural (`HomologicalComplex.homologyMap_comp_homologyIsoSc'_hom`), and exactness in a degree
is the vanishing of the homology of the short complex `sc'` there
(`HomologicalComplex.exactAt_iff_isZero_homology_sc'`).
Homology of complexes commutes with an additive functor preserving homology
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`), the complex-level form of
Mathlib's `CategoryTheory.ShortComplex.homologyFunctorIso`.
Every morphism between acyclic complexes is a quasi-isomorphism
(`HomologicalComplex.quasiIso_of_acyclic`).
-/

public section

open CategoryTheory Limits

universe w v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c} {s : K ⟶ K}

/-- A chain map of complexes in a concrete category with zero morphisms commutes with the
differentials, on elements. -/
theorem Hom.comm_apply {FC : C → C → Type*} {CC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) (i j : ι) (x : ToType (K.X i)) :
    L.d i j (φ.f i x) = φ.f j (K.d i j x) := by
  rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply]

/-- Degreewise recursion for the powers of a chain endomorphism. -/
lemma pow_f_succ (m : ℕ) (i : ι) :
    (End.of s ^ (m + 1)).asHom.f i = (End.of s ^ m).asHom.f i ≫ s.f i := by
  rw [pow_succ', End.mul_asHom, comp_f]

/-- Homological complexes have the coproducts that the underlying category has. They are
computed degreewise. -/
instance hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{w} (HomologicalComplex C c) :=
  fun _ ↦ inferInstance

/-! ### The maps onto the cycles -/

section Cycles

variable (K) {L : HomologicalComplex C c}

/-- The map from the cycles in degree `i` to the cycles in degree `j` induced by the differential
vanishes. -/
@[reassoc]
lemma iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.iCycles i ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The short complex `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` cut out of a homological complex. Its
second map is the differential with codomain restricted to the cycles in degree `j`. -/
noncomputable def cyclesShortComplex (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j)

/-- The cycle sequence is formed by the inclusion of cycles and the corestricted differential. -/
lemma cyclesShortComplex_def (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    K.cyclesShortComplex i j =
      ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j) := (rfl)

@[simp]
lemma cyclesShortComplex_X₁ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₁ = K.cycles i := (rfl)

@[simp]
lemma cyclesShortComplex_X₂ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₂ = K.X i := (rfl)

@[simp]
lemma cyclesShortComplex_X₃ (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).X₃ = K.cycles j := (rfl)

/-- The first map of the cycle sequence is the inclusion of cycles, transported along the
object equalities `cyclesShortComplex_X₁` and `cyclesShortComplex_X₂`. -/
@[simp]
lemma cyclesShortComplex_f (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).f = eqToHom (K.cyclesShortComplex_X₁ i j) ≫ K.iCycles i ≫
      eqToHom (K.cyclesShortComplex_X₂ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The second map of the cycle sequence is the corestricted differential, transported along the
object equalities `cyclesShortComplex_X₂` and `cyclesShortComplex_X₃`. -/
@[simp]
lemma cyclesShortComplex_g (i j : ι) [K.HasHomology i] [K.HasHomology j] :
    (K.cyclesShortComplex i j).g = eqToHom (K.cyclesShortComplex_X₂ i j) ≫ K.toCycles i j ≫
      eqToHom (K.cyclesShortComplex_X₃ i j).symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

variable {K}

/-- The maps onto the cycles induced by the differentials commute with morphisms of complexes. -/
@[reassoc]
lemma toCycles_cyclesMap (φ : K ⟶ L) (i j : ι) [K.HasHomology j] [L.HasHomology j] :
    K.toCycles i j ≫ cyclesMap φ j = φ.f i ≫ L.toCycles i j :=
  (cancel_mono (L.iCycles j)).1 <| by simp

/-- In a degree `j` with no nonzero differential into it, the identifications
`K.isoHomologyπ i j` of the homology with the cycles commute with the maps induced by a morphism of
complexes. -/
@[reassoc]
lemma isoHomologyπ_inv_naturality (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i) (hK : K.d i j = 0)
    (hL : L.d i j = 0) [K.HasHomology j] [L.HasHomology j] :
    homologyMap φ j ≫ (L.isoHomologyπ i j hi hL).inv =
      (K.isoHomologyπ i j hi hK).inv ≫ cyclesMap φ j := by
  rw [← cancel_epi (K.isoHomologyπ i j hi hK).hom]
  simp

variable [HasZeroObject C] [DecidableEq ι] {i : ι} {X : C}

/-- A morphism from a complex concentrated in degree `i` vanishes after the differential out of
degree `i`. -/
@[reassoc]
lemma single_f_d (g : (single C c i).obj X ⟶ L) (j : ι) : g.f i ≫ L.d i j = 0 := by
  rw [g.comm i j, single_obj_d, zero_comp]

/-- A morphism from a complex concentrated in degree `i` vanishes after the map onto the cycles in
degree `j`. -/
@[reassoc]
lemma single_f_toCycles (g : (single C c i).obj X ⟶ L) (j : ι) [L.HasHomology j] :
    g.f i ≫ L.toCycles i j = 0 := by
  rw [← cancel_mono (L.iCycles j), Category.assoc, toCycles_i, single_f_d, zero_comp]

end Cycles

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

variable (K) in
/-- The sequence `Zᵢ ⟶ Kᵢ ⟶ Zⱼ` of the cycles of a complex `K` is exact when `j` is the degree
following `i`: the cycles in degree `i` are the kernel of the differential. -/
lemma cyclesShortComplex_exact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [hH : (K.cyclesShortComplex i j).HasHomology] (hij : c.next i = j) :
    (K.cyclesShortComplex i j).Exact := by
  rw [cyclesShortComplex_def] at hH ⊢
  let S := ShortComplex.mk _ _ (K.iCycles_toCycles i j)
  have hS := isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j hij)
    (K.iCycles_toCycles i j) (K.toCycles_i i j)
  rw [S.exact_iff_iCycles_pOpcycles_zero]
  have h : hS.lift (KernelFork.ofι S.iCycles S.iCycles_g) ≫ S.f = S.iCycles :=
    Fork.IsLimit.lift_ι _
  rw [← h, Category.assoc, S.f_pOpcycles, comp_zero]

/-- A morphism killed by the differential `Kᵢ ⟶ Kⱼ` is killed by its corestriction to the
cycles in degree `j`. -/
lemma comp_toCycles_eq_zero {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) : a ≫ K.toCycles i j = 0 := by
  rw [← cancel_mono (K.iCycles j), Category.assoc, K.toCycles_i, ha, zero_comp]

/-- The corestriction `Kᵢ ⟶ Zⱼ` of the differential has the same kernel as the differential
`Kᵢ ⟶ Kⱼ`: if `A ⟶ Kᵢ ⟶ Kⱼ` is exact, then so is `A ⟶ Kᵢ ⟶ Zⱼ`. -/
lemma exact_toCycles {A : C} {i : ι} (j : ι) [K.HasHomology j] (a : A ⟶ K.X i)
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha))
    (S₂ := ShortComplex.mk a (K.d i j) ha)
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles j }).2 hex

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*}
  {c : ComplexShape ι} {K : HomologicalComplex C c}

/-- In a complex exact in degree `j`, the map onto the cycles in degree `j` from the preceding
degree is an epimorphism. -/
lemma epi_toCycles_of_exactAt {i j : ι} [K.HasHomology j]
    (h : K.ExactAt j) (hij : c.prev j = i) :
    Epi (K.toCycles i j) := by
  rw [exactAt_iff' _ i j (c.next j) hij rfl] at h
  have := h.hasHomology
  rw [← epi_comp_iff_of_isIso _ (K.cyclesIsoSc' i j (c.next j) hij rfl).hom,
    K.toCycles_cyclesIsoSc'_hom]
  exact h.epi_toCycles

/-- A morphism of complexes which is an epimorphism in degree `i = c.prev j` induces an
epimorphism on the cycles in degree `j` when its target is exact at `j`. -/
lemma epi_cyclesMap_of_exactAt {L : HomologicalComplex C c} (φ : K ⟶ L) {i j : ι}
    [K.HasHomology j] [L.HasHomology j] (hij : c.prev j = i) [Epi (φ.f i)] (hL : L.ExactAt j) :
    Epi (cyclesMap φ j) := by
  have := epi_toCycles_of_exactAt hL hij
  refine epi_of_epi_fac (f := K.toCycles i j) (h := φ.f i ≫ L.toCycles i j) ?_
  simp [← cancel_mono (L.iCycles j)]

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)` is short exact when `i` and `j` are adjacent
and `K` is exact in degree `j`. -/
lemma cyclesShortComplex_shortExact (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology]
    (hij : c.Rel i j) (hK : K.ExactAt j) : (K.cyclesShortComplex i j).ShortExact := by
  have hE := K.cyclesShortComplex_exact i j (c.next_eq' hij)
  rw [cyclesShortComplex_def] at hE ⊢
  exact ShortComplex.ShortExact.mk' hE
    inferInstance (epi_toCycles_of_exactAt hK (c.prev_eq' hij))

/-- `HomologicalComplex.cyclesShortComplex_shortExact` with the short complex written out as
`ShortComplex.mk (K.iCycles i) (K.toCycles i j) _`, so that its terms are the cycles and the term
of `K` themselves. -/
lemma shortExact_mk_iCycles_toCycles (i j : ι) [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology] (hij : c.Rel i j) (hK : K.ExactAt j) :
    (ShortComplex.mk (K.iCycles i) (K.toCycles i j) (K.iCycles_toCycles i j)).ShortExact := by
  have := K.cyclesShortComplex_shortExact i j hij hK
  rwa [cyclesShortComplex_def] at this

/-- The map `Kᵢ ⟶ Zⱼ(K)` onto the cycles is an isomorphism when `i` and `j` are adjacent, `K` is
exact in degree `j` and the cycles of `K` in degree `i` vanish. -/
lemma isIso_toCycles_of_isZero_cycles [Balanced C] {i j : ι} [K.HasHomology i] [K.HasHomology j]
    (hij : c.Rel i j) (hK : K.ExactAt j) (hZ : IsZero (K.cycles i)) :
    IsIso (K.toCycles i j) := by
  have := epi_toCycles_of_exactAt hK (c.prev_eq' hij)
  have := Preadditive.mono_of_isZero_kernel' _
    (isKernelOfComp (K.iCycles j) (K.d i j) (K.cyclesIsKernel i j (c.next_eq' hij))
      (K.iCycles_toCycles i j) (K.toCycles_i i j)) hZ
  exact isIso_of_mono_of_epi _

/-- The cycle sequence `Zᵢ(K) ⟶ Kᵢ ⟶ Zⱼ(K)`, with its outer terms replaced along isomorphisms
`X ≅ Zᵢ(K)` and `Zⱼ(K) ≅ Y`, is short exact when `i` and `j` are adjacent and `K` is exact in
degree `j`. -/
lemma cyclesShortComplex_shortExact_of_iso {i j : ι} [K.HasHomology i] [K.HasHomology j]
    [(K.cyclesShortComplex i j).HasHomology] (hij : c.Rel i j) (hK : K.ExactAt j) {X Y : C}
    (e : X ≅ K.cycles i) (e' : K.cycles j ≅ Y) :
    (ShortComplex.mk (e.hom ≫ K.iCycles i) (K.toCycles i j ≫ e'.hom)
      (by simp [iCycles_toCycles_assoc])).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk e.symm (Iso.refl (K.X i)) e') <|
    K.cyclesShortComplex_def i j ▸ K.cyclesShortComplex_shortExact i j hij hK

/-- A monomorphism `A ⟶ Kᵢ` onto the kernel of the differential `Kᵢ ⟶ Kⱼ` fits into a short exact
sequence `0 ⟶ A ⟶ Kᵢ ⟶ Zⱼ ⟶ 0` when `i` precedes `j` and `K` is exact in degree `j`. -/
lemma shortExact_toCycles {A : C} {i j : ι} [K.HasHomology j] (a : A ⟶ K.X i) [Mono a]
    (ha : a ≫ K.d i j = 0) (hex : (ShortComplex.mk a (K.d i j) ha).Exact)
    (hij : c.prev j = i) (hK : K.ExactAt j) :
    (ShortComplex.mk a (K.toCycles i j) (comp_toCycles_eq_zero j a ha)).ShortExact :=
  have := epi_toCycles_of_exactAt hK hij
  { exact := exact_toCycles j a ha hex }

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C] (K : CochainComplex C ℕ)
  [K.HasHomology 0] [K.HasHomology 1]

/-- The map `K⁰ ⟶ Z¹(K)` onto the cycles in degree `1` is an isomorphism when `K` is exact in
degrees `0` and `1`, since the cycles `Z⁰(K) ≅ H⁰(K)` then vanish. -/
lemma isIso_toCycles_zero_of_exactAt (h₀ : K.ExactAt 0) (h₁ : K.ExactAt 1) :
    IsIso (K.toCycles 0 1) :=
  K.isIso_toCycles_of_isZero_cycles (by simp) h₁
    (((K.exactAt_iff_isZero_homology 0).1 h₀).of_iso K.isoHomologyπ₀)

/-- A monomorphism of nonnegative cochain complexes that is an isomorphism in degree zero
induces an isomorphism on zeroth cohomology. -/
lemma isIso_homologyMap_zero_of_mono {D : Type*} [Category* D] [Abelian D]
    {K L : CochainComplex D ℕ} (f : K ⟶ L) [Mono f] [IsIso (f.f 0)] :
    IsIso (HomologicalComplex.homologyMap f 0) := by
  -- Complex homology is defined as homology of the three-term short complex at this degree.
  change IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ 0).map f))
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · -- The first component is evaluated at `prev 0`, which is zero for the nonnegative shape.
    change Epi (f.f ((ComplexShape.up ℕ).prev 0))
    have hp : (ComplexShape.up ℕ).prev 0 = 0 :=
      (ComplexShape.up ℕ).prev_eq_self' 0 (by simp)
    rw [hp]
    infer_instance
  · -- The middle short-complex component is the map on zero cochains by definition.
    change IsIso (f.f 0)
    infer_instance
  · -- The last component is evaluation in the next degree; evaluation preserves monomorphisms.
    change Mono (f.f ((ComplexShape.up ℕ).next 0))
    infer_instance

end CochainComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- A morphism of complexes that vanishes in degree `i` induces zero on homology in degree `i`. -/
lemma homologyMap_eq_zero_of_f_eq_zero (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (h : φ.f i = 0) : homologyMap φ i = 0 := by
  have hc : cyclesMap φ i = 0 := by
    rw [← cancel_mono (L.iCycles i), cyclesMap_i, h, comp_zero, zero_comp]
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, hc, zero_comp, comp_zero]

/-- Two morphisms of complexes that agree on the cycles in degree `i` induce the same map on
homology in degree `i`. -/
lemma homologyMap_eq_of_iCycles_comp {f g : K ⟶ L} {i : ι} [K.HasHomology i] [L.HasHomology i]
    (h : K.iCycles i ≫ f.f i = K.iCycles i ≫ g.f i) : homologyMap f i = homologyMap g i := by
  have hc : cyclesMap f i = cyclesMap g i := by
    rw [← cancel_mono (L.iCycles i), cyclesMap_i, cyclesMap_i, h]
  rw [← cancel_epi (K.homologyπ i), homologyπ_naturality, homologyπ_naturality, hc]

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- If a complex is exact in degrees `i` and `j`, with `c.Rel i j`, the map from the opcycles in
degree `i` to the cycles in degree `j` is an isomorphism, by the exact sequence
`Hⁱ ⟶ opcyclesⁱ ⟶ Zʲ ⟶ Hʲ`. -/
lemma isIso_opcyclesToCycles {i j : ι} (hij : c.Rel i j) (hi : K.ExactAt i) (hj : K.ExactAt j) :
    IsIso (K.opcyclesToCycles i j) := by
  have h := HomologySequence.composableArrows₃_exact K i j hij
  have : Mono (K.opcyclesToCycles i j) :=
    (h.exact 0).mono_g (hi.isZero_homology.eq_of_src _ _)
  have : Epi (K.opcyclesToCycles i j) :=
    (h.exact 1).epi_f (hj.isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end HomologicalComplex

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

/-- Taking cycles is additive on morphisms of complexes. -/
@[simp]
lemma cyclesMap_add (f g : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i := by
  apply (cancel_mono (L.iCycles i)).1
  simp only [Preadditive.add_comp, cyclesMap_i, add_f_apply, Preadditive.comp_add]

instance cyclesFunctor_additive [CategoryWithHomology C] (i : ι) :
    (cyclesFunctor C c i).Additive where
  map_add := by
    intro X Y f g
    -- `cyclesFunctor` is opaque, so expose its defining map before applying the map-level API.
    change cyclesMap (f + g) i = cyclesMap f i + cyclesMap g i
    exact cyclesMap_add f g i

section HomologyIsoSc'

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
  {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L) (i j k : ι)
  (hi : c.prev j = i) (hk : c.next j = k) [K.HasHomology j] [L.HasHomology j]
  [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology]

/-- The isomorphisms `homologyIsoSc'` are natural (this is the naturality of Mathlib's
`homologyFunctorIso'`, for complexes which only individually have homology). -/
@[reassoc]
lemma homologyMap_comp_homologyIsoSc'_hom :
    homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) := by
  rw [homologyIsoSc', homologyIsoSc', ShortComplex.homologyMapIso_hom,
    ShortComplex.homologyMapIso_hom, homologyMap]
  -- the source of `homologyMap f j` is `K.homology j`, which is `(K.sc j).homology` only up to
  -- unfolding `HomologicalComplex.homology`, so the generic `homologyMap_comp` needs `erw`
  erw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact (natIsoSc' C c i j k hi hk).hom.naturality f

end HomologyIsoSc'

/-- A homological complex is exact at `j` exactly when the homology of its short complex at `j`,
with explicit neighbouring indices, is zero. -/
lemma exactAt_iff_isZero_homology_sc' {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*}
    {c : ComplexShape ι} (L : HomologicalComplex C c) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) [(L.sc' i j k).HasHomology] :
    L.ExactAt j ↔ IsZero (L.sc' i j k).homology :=
  (exactAt_iff' L i j k hi hk).trans (ShortComplex.exact_iff_isZero_homology _)

end HomologicalComplex

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {K L : ChainComplex C ℕ} [K.HasHomology 0] [L.HasHomology 0]

/-- The identification of degree-zero chains with degree-zero cycles is natural. -/
@[reassoc]
lemma cycles₀Iso_inv_naturality (φ : K ⟶ L) :
    K.cycles₀Iso.inv ≫ HomologicalComplex.cyclesMap φ 0 =
      φ.f 0 ≫ L.cycles₀Iso.inv := by
  apply (cancel_mono (L.iCycles 0)).1
  simp

/-- The passage from degree-zero chains to degree-zero homology, through the identification of
the homology with the opcycles, is natural. -/
@[reassoc]
lemma pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap (φ : K ⟶ L) :
    K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ HomologicalComplex.homologyMap φ 0 =
      φ.f 0 ≫ L.pOpcycles 0 ≫ L.isoHomologyι₀.inv := by
  rw [ChainComplex.isoHomologyι₀_inv_naturality, HomologicalComplex.p_opcyclesMap_assoc]

end ChainComplex

namespace HomologicalComplex

section HomologyTransport

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {ι : Type*} {c : ComplexShape ι} {L L' M M' : HomologicalComplex C c}

/-- A morphism transported along equalities of complexes induces the corresponding transport
of the homology map. -/
lemma homologyMap_comp_eqToHom (ψ : L ⟶ L') (hM : M = L) (hM' : M' = L')
    (τ : M ⟶ M') (hτ : τ = eqToHom hM ≫ ψ ≫ eqToHom hM'.symm) (q : ι) :
    homologyMap τ q ≫ eqToHom (congrArg (·.homology q) hM') =
      eqToHom (congrArg (·.homology q) hM) ≫ homologyMap ψ q := by
  subst hM hM' hτ
  simp

end HomologyTransport

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}

/-- A morphism between acyclic homological complexes is a quasi-isomorphism. -/
lemma quasiIso_of_acyclic {K L : HomologicalComplex C c} (f : K ⟶ L) [∀ i, K.HasHomology i]
    [∀ i, L.HasHomology i] (hK : K.Acyclic) (hL : L.Acyclic) : QuasiIso f :=
  (quasiIso_iff f).2 fun i ↦ (quasiIsoAt_iff_exactAt f i (hK i)).2 (hL i)

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- Homology of homological complexes commutes with a functor preserving homology. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  -- the short complex of `F` applied to `K` in degree `i` is `F` applied to that of `K`
  isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c i) (ShortComplex.homologyFunctorIso F)

@[simp]
lemma mapHomologicalComplexCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K =
      ((K.sc i).mapHomologyIso F).hom :=
  (rfl)

end CategoryTheory.Functor

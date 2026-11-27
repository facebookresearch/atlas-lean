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
TauCeti/Algebra/Homology/ModuleCat/Basic.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RingTheory.Finiteness.Defs
public import MathlibExt.Algebra.Homology.CyclicComplexHomology
public import MathlibExt.LinearAlgebra.CyclicLocallyNilpotent

/-!
# Cycles and homology of homological complexes of modules

For a homological complex `K` of modules over a ring, the inclusion of the degree-`n` cycles into
`K.X n` is injective and the class map from the cycles onto the degree-`n` homology is surjective.
These are the elementwise forms of the facts that `K.iCycles n` is a monomorphism and
`K.homologyπ n` is an epimorphism.  Chain maps commute with the differentials and the square of
the differential vanishes, on elements (`HomologicalComplex.Hom.comm_apply`,
`HomologicalComplex.d_comp_d_apply`), cycles have zero boundary, on elements
(`HomologicalComplex.iCycles_d_apply`), and an element killed by the differential to degree
`c.next i` is killed by every differential out of degree `i`
(`HomologicalComplex.d_apply_eq_zero_of_d_next_apply_eq_zero`).  Conversely, an element of
`K.X n` killed by the differential is a cycle, `HomologicalComplex.moduleCatCyclesMk`.  This
constructor directly returns an element of `K.cycles n` for modules over a ring in any universe,
whereas Mathlib's `HomologicalComplex.cyclesMk` returns an element of
`(forget₂ C Ab).obj (K.cycles n)`.
A linear map into `K.X n` whose values are cycles induces a class map into the homology,
`HomologicalComplex.moduleCatHomologyClass`; it is surjective when every cycle is a value, its
kernel consists of the elements sent to boundaries, and chain maps act on it compatibly.
Consequently, when `K` is the union of subcomplexes `L i`, every homology class of `K` comes from
some `L i` (`HomologicalComplex.exists_homologyMap_eq_of_injective`), and a class of `L i` that
vanishes in `K` already vanishes in a larger subcomplex containing every boundary it needs
(`HomologicalComplex.exists_homologyMap_eq_zero_of_injective`).  Two cycles whose difference
is a boundary have the same homology class
(`HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d`); conversely, cycles with the same
class differ by the boundary of an element of degree `c.prev n`
(`HomologicalComplex.moduleCat_homologyπ_eq_iff`), and a cycle has zero homology class exactly
when it is a boundary (`HomologicalComplex.moduleCat_homologyπ_eq_zero_iff`); where no
differential enters, such as in degree zero of a cochain complex, a cycle with zero class is zero
(`HomologicalComplex.moduleCat_eq_zero_of_homologyπ_eq_zero`).
When the homology is finitely generated, finitely many cycles generate all cycles modulo
boundaries (`HomologicalComplex.exists_fin_moduleCat_cycles_generating`).
Cycles are elements of the kernel of the outgoing differential
(`HomologicalComplex.moduleCatCyclesToKer`), that kernel has a homology class map
(`HomologicalComplex.moduleCatKerHomologyClass`), surjective and compatible with chain maps
(`HomologicalComplex.homologyMap_moduleCatKerHomologyClass`), and the image of the incoming
differential, the kernel and the homology form an exact sequence
(`HomologicalComplex.exact_inclusion_moduleCatKerHomologyClass`).
Given concrete cocycle and coboundary submodules identified with the terms of a cochain complex,
`HomologicalComplex.moduleCatCohomologyClassOfIso` specializes this class map to the cocycles,
with its surjectivity and its kernel described by the coboundaries.  When the differential is a
linear map `δ` under these identifications, the kernels of `δ` and the coboundaries `0, im δ, …`
satisfy the hypotheses of this construction (`HomologicalComplex.moduleCat_d_inv_eq_zero_iff`,
`HomologicalComplex.moduleCat_mem_iff_exists_d_eq_inv`).  A complex of modules is exact
in a degree exactly when the image of the incoming differential is the kernel of the outgoing one
(`HomologicalComplex.exactAt_iff_range_eq_ker`). At a degree where the complex is exact, the
image of the incoming differential, the term and the image of the outgoing differential form a
short exact sequence (`HomologicalComplex.exact_subtype_rangeRestrict`).
A chain map restricts to a map between the images of the differentials
(`HomologicalComplex.Hom.boundaryMap`), functorially in the chain map
(`HomologicalComplex.Hom.boundaryMap_comp`), zero on the image of a zero differential
(`HomologicalComplex.Hom.boundaryMap_eq_zero`), and injective where the chain map is; for a
degreewise short exact sequence of complexes whose third term is exact, these maps form a sequence
exact in the middle (`HomologicalComplex.Hom.exact_boundaryMap`).  A family of chain endomorphisms
that is locally nilpotent on the degree-`n` term is locally nilpotent on the degree-`n` homology
(`HomologicalComplex.iSup_wordKer_homologyMap_eq_top`), since the homology is a quotient of the
cycles, a submodule of the term.

For a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of complexes of modules, the connecting map
sends the class of a cycle of `X₃` with lift `x₂` to the class of the cycle of `X₁` mapping to
`d x₂` (`CategoryTheory.ShortComplex.ShortExact.moduleCat_δ_homologyπ`). Conversely, if a cycle
`z₁` of `X₁` represents the image of a class `x₃` under the connecting map, then `x₃` is
represented by the image of an element `x₂` of `X₂` whose differential is exactly the image of
`z₁` (`CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_d_eq_of_δ_eq`), and such `x₂` is
unique up to boundaries and images of cycles of `X₁`
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_exists_sub_eq_d_add`). For the chains of a
pair of spaces, this produces chains relative to a subspace with a prescribed boundary in the
subspace, such as fundamental chains of a manifold with boundary.
-/

public section

open CategoryTheory

namespace HomologicalComplex

/-- Homology maps commute with the class map from cycles, on elements of complexes of modules.

Not `@[simp]`: it would make the existing simp lemmas
`ChainComplex.homologyMap_linearYonedaObjMap_homologyπ_apply` and
`TopCat.singularCohomologyMap_homologyπ_constSingularCocycle` fail `simpNF`. -/
theorem moduleCat_homologyMap_homologyπ {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L) (i : ι) (x : K.cycles i) :
    homologyMap φ i (K.homologyπ i x) = L.homologyπ i (cyclesMap φ i x) := by
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply]

/-- A chain map of complexes of modules sends cycles to cycles, on elements. -/
theorem Hom.d_apply_eq_zero_of_d_apply_eq_zero {R : Type*} [Ring R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L) (i j : ι)
    (x : K.X i) (hx : (K.d i j).hom x = 0) : (L.d i j).hom ((φ.f i).hom x) = 0 :=
  (Hom.comm_apply φ i j x).trans ((congrArg _ hx).trans (map_zero _))

/-- In a complex of modules the differential of a differential vanishes, on elements. -/
theorem d_comp_d_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j l : ι) (x : K.X i) :
    K.d j l (K.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

/-- In a complex of modules a cycle has zero boundary, on elements. -/
theorem iCycles_d_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j : ι) (z : K.cycles i) :
    K.d i j (K.iCycles i z) = 0 :=
  (ConcreteCategory.comp_apply _ _ z).symm.trans (ConcreteCategory.congr_hom (K.iCycles_d i j) z)

/-- In a complex of modules, an element killed by the differential to degree `c.next i` is killed
by every differential out of degree `i`. -/
theorem d_apply_eq_zero_of_d_next_apply_eq_zero {R : Type*} [Ring R] {ι : Type*}
    {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat R) c) {i j : ι} (hj : c.next i = j)
    {x : K.X i} (hx : K.d i j x = 0) (l : ι) : K.d i l x = 0 := by
  by_cases hl : c.Rel i l
  · obtain rfl := hj.symm.trans (c.next_eq' hl)
    exact hx
  · simp [K.shape i l hl]

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

/-- A complex of modules is exact in degree `j` exactly when the image of the incoming
differential `K.X i ⟶ K.X j` is the kernel of the outgoing differential `K.X j ⟶ K.X k`. -/
theorem exactAt_iff_range_eq_ker {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k) :
    K.ExactAt j ↔ LinearMap.range (K.d i j).hom = LinearMap.ker (K.d j k).hom :=
  (K.exactAt_iff' i j k hi hk).trans (ShortComplex.moduleCat_exact_iff_range_eq_ker _)

variable {K} in
/-- At a degree `j` where a complex of modules is exact, the inclusion of the image of the incoming
differential `K.X i ⟶ K.X j` and the corestriction of the outgoing differential `K.X j ⟶ K.X k` to
its image form a short exact sequence. -/
theorem exact_subtype_rangeRestrict {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (h : K.ExactAt j) :
    Function.Exact (LinearMap.range (K.d i j).hom).subtype (K.d j k).hom.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact ((K.exactAt_iff_range_eq_ker hi hk).1 h).symm

section BoundaryMap

variable {K L M : HomologicalComplex (ModuleCat R) c}

/-- A chain map of complexes of modules sends the image of the differential `K.X i ⟶ K.X j` into
the image of the differential `L.X i ⟶ L.X j`. -/
def Hom.boundaryMap (φ : K ⟶ L) (i j : ι) :
    LinearMap.range (K.d i j).hom →ₗ[R] LinearMap.range (L.d i j).hom :=
  (φ.f j).hom.restrict fun _ ⟨y, hy⟩ ↦ ⟨(φ.f i).hom y, by rw [Hom.comm_apply, hy]⟩

/-- The map on boundaries induced by a chain map is the restriction of the chain map. -/
@[simp]
theorem Hom.coe_boundaryMap (φ : K ⟶ L) (i j : ι) (x : LinearMap.range (K.d i j).hom) :
    (φ.boundaryMap i j x : L.X j) = (φ.f j).hom x :=
  (rfl)

/-- The identity chain map induces the identity on boundaries. -/
@[simp]
theorem Hom.boundaryMap_id (i j : ι) : (𝟙 K : K ⟶ K).boundaryMap i j = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- The map on boundaries induced by a composite of chain maps is the composite of the induced
maps. -/
@[simp]
theorem Hom.boundaryMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) (i j : ι) :
    (φ ≫ ψ).boundaryMap i j = ψ.boundaryMap i j ∘ₗ φ.boundaryMap i j :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- If the differential `K.X i ⟶ K.X j` vanishes, the map on its image induced by a chain map is
zero. -/
@[simp]
theorem Hom.boundaryMap_eq_zero (φ : K ⟶ L) {i j : ι} (h : K.d i j = 0) :
    φ.boundaryMap i j = 0 :=
  LinearMap.ext fun ⟨_, x, hx⟩ ↦ Subtype.ext <| by simp [← hx, h]

/-- A chain map that is injective in degree `j` is injective on the boundaries of degree `j`. -/
theorem Hom.boundaryMap_injective (φ : K ⟶ L) (i : ι) {j : ι}
    (hφ : Function.Injective (φ.f j).hom) : Function.Injective (φ.boundaryMap i j) :=
  fun _ _ hxy ↦ Subtype.ext (hφ (congrArg Subtype.val hxy))

/-- Let `K ⟶ L ⟶ M` be chain maps of complexes of modules, let `h = c.prev i` and
`j = c.next i`. If the sequence `K ⟶ L ⟶ M` is exact in degree `i`, `L ⟶ M` is
surjective in degree `h` and `M` is exact in degree `i`, then the induced maps on the images of
the differentials `K.X i ⟶ K.X j`, `L.X i ⟶ L.X j` and `M.X i ⟶ M.X j` form a sequence that is
exact in the middle. -/
theorem Hom.exact_boundaryMap {φ : K ⟶ L} {ψ : L ⟶ M} {h i j : ι} (hh : c.prev i = h)
    (hj : c.next i = j) (hi : Function.Exact (φ.f i).hom (ψ.f i).hom)
    (hψ : Function.Surjective (ψ.f h).hom) (hM : M.ExactAt i) :
    Function.Exact (φ.boundaryMap i j) (ψ.boundaryMap i j) := by
  rintro ⟨_, x, rfl⟩
  constructor
  · intro hx
    have hx' : (M.d i j).hom ((ψ.f i).hom x) = 0 := by
      rw [Hom.comm_apply]
      exact congrArg Subtype.val hx
    -- The image of `x` in `M.X i` is a cycle, hence the boundary of some `ψ w`; then
    -- `x - d w` comes from `K.X i` and has the same boundary as `x`.
    obtain ⟨⟨_, z, rfl⟩, hz⟩ := ((exact_subtype_rangeRestrict hh hj hM) _).1 (Subtype.ext hx')
    obtain ⟨w, rfl⟩ := hψ z
    obtain ⟨x', hx''⟩ := (hi (x - (L.d h i).hom w)).1 (by
      rw [map_sub, ← Hom.comm_apply, sub_eq_zero]
      exact hz.symm)
    refine ⟨⟨(K.d i j).hom x', x', rfl⟩, Subtype.ext ?_⟩
    rw [coe_boundaryMap, ← Hom.comm_apply, hx'', map_sub, d_comp_d_apply, sub_zero]
  · rintro ⟨⟨_, y, rfl⟩, hx'⟩
    rw [← hx']
    refine Subtype.ext ?_
    simp only [coe_boundaryMap, ← Hom.comm_apply, hi.apply_apply_eq_zero, map_zero]
    rfl

end BoundaryMap

/-- The inclusion of the degree-`n` cycles of a homological complex of modules into its degree-`n`
term is injective. -/
lemma moduleCat_iCycles_injective : Function.Injective (K.iCycles n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The class map from the degree-`n` cycles of a homological complex of modules onto its
degree-`n` homology is surjective. -/
lemma moduleCat_homologyπ_surjective : Function.Surjective (K.homologyπ n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The differential out of degree `n` of a complex of modules kills every cycle of degree `n`, on
elements. -/
@[simp]
lemma moduleCat_d_iCycles_apply (m : ι) (z : K.cycles n) : K.d n m (K.iCycles n z) = 0 := by
  rw [← ModuleCat.comp_apply, K.iCycles_d]
  rfl

/-- The underlying element of the cycle `K.toCycles m n y` is the image `K.d m n y`, on
elements of complexes of modules. -/
@[simp]
lemma moduleCat_iCycles_toCycles_apply (m : ι) (y : K.X m) :
    K.iCycles n (K.toCycles m n y) = K.d m n y := by
  rw [← ModuleCat.comp_apply, toCycles_i]

/-- A chain map of complexes of modules acts on cycles as it does on the underlying elements. -/
@[simp]
lemma moduleCat_iCycles_cyclesMap_apply {L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)
    (z : K.cycles n) : L.iCycles n (cyclesMap φ n z) = φ.f n (K.iCycles n z) := by
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply]

variable {n} in
/-- A degree-`n` cycle of a homological complex of modules has zero homology class exactly when it
is a boundary, the image of an element of the term of degree `c.prev n`. -/
lemma moduleCat_homologyπ_eq_zero_iff {m : ι} (hm : c.prev n = m) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔ ∃ y : K.X m, K.toCycles m n y = z := by
  refine ⟨(ShortComplex.moduleCat_exact_iff _).1 (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles m n) (K.homologyπ n) (K.toCycles_comp_homologyπ m n))
    (K.homologyIsCokernel m n hm)) z, ?_⟩
  rintro ⟨y, rfl⟩
  rw [← ModuleCat.comp_apply, toCycles_comp_homologyπ]
  rfl

variable {n} in
/-- A degree-`n` cycle of a homological complex of modules with zero homology class vanishes when
no differential enters degree `n`, for instance in degree zero of an `ℕ`-indexed cochain complex:
there are no boundaries. -/
lemma moduleCat_eq_zero_of_homologyπ_eq_zero (hn : ¬ c.Rel (c.prev n) n) (z : K.cycles n)
    (hz : K.homologyπ n z = 0) : z = 0 := by
  have := K.isIso_homologyπ (c.prev n) n rfl (K.shape _ _ hn)
  exact (ModuleCat.mono_iff_injective _).1 inferInstance (hz.trans (map_zero _).symm)

variable {n} in
/-- Two degree-`n` cycles of a complex of modules have the same homology class exactly when the
difference of their underlying elements is a boundary, the image of an element of the term of
degree `c.prev n`. -/
lemma moduleCat_homologyπ_eq_iff {m : ι} (hm : c.prev n = m) (z w : K.cycles n) :
    K.homologyπ n z = K.homologyπ n w ↔ ∃ y : K.X m, K.d m n y = K.iCycles n z - K.iCycles n w := by
  rw [← sub_eq_zero, ← map_sub, K.moduleCat_homologyπ_eq_zero_iff hm]
  refine exists_congr fun y ↦ ?_
  rw [← (K.moduleCat_iCycles_injective n).eq_iff, map_sub, moduleCat_iCycles_toCycles_apply]

variable {n} in
/-- An element `x` of `K.X n` killed by the differential `K.d n m` out of degree `n`, as a cycle
of degree `n`. -/
noncomputable def moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by subst hm; exact hx⟩

/-- The cycle `K.moduleCatCyclesMk x m hm hx` has underlying element `x`. -/
@[simp]
lemma iCycles_moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.iCycles n (K.moduleCatCyclesMk x m hm hx) = x :=
  (K.sc n).moduleCatCyclesIso_inv_iCycles_apply _

section HomologyClass

variable {n} {m : ι} (hm : c.next n = m) {Z : Type*} [AddCommGroup Z] [Module R Z]
  (j : Z →ₗ[R] K.X n) (hj : ∀ z, K.d n m (j z) = 0)

/-- The homology class map of a linear map `j` into the degree-`n` term of a complex of modules
whose values are cycles. The source of `j` need not be a submodule of a module identified with the
term, so subcomplexes are covered. -/
noncomputable def moduleCatHomologyClass : Z →ₗ[R] K.homology n :=
  (K.homologyπ n).hom ∘ₗ (K.sc n).moduleCatCyclesIso.inv.hom ∘ₗ
    j.codRestrict _ fun z ↦ by subst hm; exact hj z

/-- The class of `z` is the homology class of the cycle `j z`. -/
lemma moduleCatHomologyClass_apply (z : Z) :
    K.moduleCatHomologyClass hm j hj z =
      K.homologyπ n (K.moduleCatCyclesMk (j z) m hm (hj z)) :=
  (rfl)

/-- If every degree-`n` cycle is a value of `j`, then every homology class is the class of an
element. -/
lemma moduleCatHomologyClass_surjective (h : ∀ x : K.X n, K.d n m x = 0 → ∃ z, j z = x) :
    Function.Surjective (K.moduleCatHomologyClass hm j hj) := by
  intro x
  obtain ⟨y, rfl⟩ := K.moduleCat_homologyπ_surjective n x
  obtain ⟨z, hz⟩ := h (K.iCycles n y) <| by
    subst hm
    exact K.moduleCat_d_iCycles_apply n _ y
  refine ⟨z, ?_⟩
  rw [moduleCatHomologyClass_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [iCycles_moduleCatCyclesMk, hz]

/-- The class of `z` vanishes exactly when `j z` is a boundary, the image of an element of the
term of degree `c.prev n`. -/
lemma moduleCatHomologyClass_eq_zero_iff {p : ι} (hp : c.prev n = p) (z : Z) :
    K.moduleCatHomologyClass hm j hj z = 0 ↔ ∃ y : K.X p, K.d p n y = j z := by
  rw [moduleCatHomologyClass_apply, ← map_zero (K.homologyπ n).hom,
    K.moduleCat_homologyπ_eq_iff hp, iCycles_moduleCatCyclesMk, map_zero, sub_zero]

variable {K} in
/-- A chain map `φ` sends the class of `z` to the class of `g z` when it carries `j z` to
`j' (g z)`. -/
lemma homologyMap_moduleCatHomologyClass {L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)
    {Z' : Type*} [AddCommGroup Z'] [Module R Z'] (j' : Z' →ₗ[R] L.X n)
    (hj' : ∀ z, L.d n m (j' z) = 0) (g : Z →ₗ[R] Z') (h : ∀ z, φ.f n (j z) = j' (g z)) (z : Z) :
    homologyMap φ n (K.moduleCatHomologyClass hm j hj z) =
      L.moduleCatHomologyClass hm j' hj' (g z) := by
  rw [moduleCatHomologyClass_apply, moduleCatHomologyClass_apply, ← ModuleCat.comp_apply,
    homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply L.moduleCat_iCycles_injective n
  rw [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk,
    iCycles_moduleCatCyclesMk, h]

end HomologyClass

section KerHomologyClass

/-- In a complex of modules the image of the incoming differential `K.d p n` is contained in the
kernel of the outgoing differential `K.d n m`. -/
theorem range_d_le_ker_d (p m : ι) :
    LinearMap.range (K.d p n).hom ≤ LinearMap.ker (K.d n m).hom := by
  rintro _ ⟨x, rfl⟩
  exact K.d_comp_d_apply _ _ _ x

/-- A degree-`n` cycle of a complex of modules, as an element of the kernel of the differential
`K.d n m`. -/
noncomputable def moduleCatCyclesToKer (m : ι) : K.cycles n →ₗ[R] LinearMap.ker (K.d n m).hom :=
  (K.iCycles n).hom.codRestrict _ fun y ↦ by
    exact K.moduleCat_d_iCycles_apply n m y

/-- The element of the kernel of `K.d n m` given by a cycle `y` is `K.iCycles n y`. -/
@[simp]
lemma coe_moduleCatCyclesToKer (m : ι) (y : K.cycles n) :
    (K.moduleCatCyclesToKer n m y : K.X n) = K.iCycles n y :=
  (rfl)

variable {n} {m : ι} (hm : c.next n = m)

/-- The homology class of an element of the kernel of the outgoing differential `K.d n m`. -/
noncomputable def moduleCatKerHomologyClass : LinearMap.ker (K.d n m).hom →ₗ[R] K.homology n :=
  K.moduleCatHomologyClass hm (Submodule.subtype _) fun z ↦ LinearMap.mem_ker.1 z.2

/-- The kernel class map is the homology class map of the kernel's inclusion into the term. -/
lemma moduleCatKerHomologyClass_eq_moduleCatHomologyClass :
    K.moduleCatKerHomologyClass hm =
      K.moduleCatHomologyClass hm (Submodule.subtype _) (fun z ↦ z.2) :=
  (rfl)

/-- The homology class of the kernel element given by a cycle `y` is the class of `y`. -/
@[simp]
lemma moduleCatKerHomologyClass_moduleCatCyclesToKer (y : K.cycles n) :
    K.moduleCatKerHomologyClass hm (K.moduleCatCyclesToKer n m y) = K.homologyπ n y := by
  rw [moduleCatKerHomologyClass, moduleCatHomologyClass_apply]
  congr 1
  exact K.moduleCat_iCycles_injective _
    ((K.iCycles_moduleCatCyclesMk _ _ _ _ _).trans (K.coe_moduleCatCyclesToKer n m y))

/-- Every homology class is the class of an element of the kernel of the outgoing differential. -/
lemma moduleCatKerHomologyClass_surjective :
    Function.Surjective (K.moduleCatKerHomologyClass hm) := by
  rw [moduleCatKerHomologyClass]
  exact K.moduleCatHomologyClass_surjective hm _ _ fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩

variable {K} in
/-- A chain map `φ` sends the homology class of an element `z` of the kernel of `K.d n m` to the
homology class of `φ z`. -/
@[simp]
lemma homologyMap_moduleCatKerHomologyClass {L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)
    (z : LinearMap.ker (K.d n m).hom) :
    homologyMap φ n (K.moduleCatKerHomologyClass hm z) =
      L.moduleCatKerHomologyClass hm
        ⟨φ.f n z, φ.d_apply_eq_zero_of_d_apply_eq_zero n m z z.2⟩ := by
  rw [moduleCatKerHomologyClass, moduleCatKerHomologyClass]
  exact homologyMap_moduleCatHomologyClass hm _ _ φ _ _
    ((φ.f n).hom.restrict (φ.d_apply_eq_zero_of_d_apply_eq_zero n m)) (fun _ ↦ rfl) z

/-- The boundaries, the cycles and the homology in degree `n` form an exact sequence: the kernel
of the homology class map on the kernel of `K.d n m` is the image of the incoming differential. -/
theorem exact_inclusion_moduleCatKerHomologyClass {p : ι} (hp : c.prev n = p) :
    Function.Exact (Submodule.inclusion (K.range_d_le_ker_d n p m))
      (K.moduleCatKerHomologyClass hm) := by
  intro z
  rw [moduleCatKerHomologyClass, K.moduleCatHomologyClass_eq_zero_iff _ _ _ hp]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨_, y, rfl⟩, Subtype.ext hy⟩
  · rintro ⟨⟨_, y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

end KerHomologyClass

section CochainPresentation

variable (K : CochainComplex (ModuleCat R) ℕ)
variable (V : ℕ → Type*) [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
variable (Z B : ∀ n, Submodule R (V n))
variable (e : ∀ n, K.X n ≅ ModuleCat.of R (V n))
variable (hZ : ∀ (n : ℕ) (z : V n),
  z ∈ Z n ↔ K.d n (n + 1) ((e n).inv z) = 0)
variable (hB : ∀ (n : ℕ) (z : V n),
  z ∈ B n ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
    K.d ((ComplexShape.up ℕ).prev n) n y = (e n).inv z)

section Differential

variable {V e} (δ : ∀ n, V n →ₗ[R] V (n + 1))
  (hδ : ∀ n, K.d n (n + 1) ≫ (e (n + 1)).hom = (e n).hom ≫ ModuleCat.ofHom (δ n))
include hδ

/-- If the differential is `δ` under the identifications `e` of the terms, then an element of
`V n` is killed by `δ n` exactly when the differential kills its transport into the complex. -/
lemma moduleCat_d_inv_eq_zero_iff {n : ℕ} (z : V n) :
    K.d n (n + 1) ((e n).inv z) = 0 ↔ δ n z = 0 := by
  have h := ConcreteCategory.congr_hom (hδ n) ((e n).inv z)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, Iso.inv_hom_id_apply, ModuleCat.ofHom_apply] at h
  rw [← h]
  exact ⟨fun h0 ↦ by rw [h0, map_zero], fun h0 ↦ by
    rw [← Iso.hom_inv_id_apply (e (n + 1)) (K.d n (n + 1) _), h0, map_zero]⟩

/-- If the differential is `δ` under the identifications `e` of the terms, and `B` consists of
`0` in degree zero and of the image of `δ n` in degree `n + 1`, then `B` consists exactly of the
elements whose transport into the complex is in the image of the incoming differential. -/
lemma moduleCat_mem_iff_exists_d_eq_inv (hB₀ : B 0 = ⊥)
    (hB_succ : ∀ n, B (n + 1) = LinearMap.range (δ n)) (n : ℕ) (z : V n) :
    z ∈ B n ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
      K.d ((ComplexShape.up ℕ).prev n) n y = (e n).inv z := by
  cases n with
  | zero =>
    rw [hB₀, Submodule.mem_bot, CochainComplex.prev_nat_zero, K.shape 0 0 (by simp)]
    refine ⟨fun hz ↦ ⟨0, by rw [hz, map_zero, map_zero]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    rw [← Iso.inv_hom_id_apply (e 0) z, ← hy]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  | succ n =>
    have h (y : K.X n) : (e (n + 1)).hom (K.d n (n + 1) y) = δ n ((e n).hom y) := by
      rw [← ModuleCat.comp_apply, hδ n, ModuleCat.comp_apply, ModuleCat.ofHom_apply]
    rw [hB_succ, LinearMap.mem_range, CochainComplex.prev_nat_succ]
    constructor
    · rintro ⟨ψ, rfl⟩
      refine ⟨(e n).inv ψ, ?_⟩
      rw [← Iso.hom_inv_id_apply (e (n + 1)) (K.d n (n + 1) _), h, Iso.inv_hom_id_apply]
    · rintro ⟨y, hy⟩
      exact ⟨(e n).hom y, by rw [← h, hy, Iso.inv_hom_id_apply]⟩

end Differential

/-- The linear map sending a cocycle of a cochain complex of modules to its cohomology class, the
homology class map of the cocycles transported through the chosen identifications of the terms. -/
noncomputable def moduleCatCohomologyClassOfIso (n : ℕ) : Z n →ₗ[R] K.homology n :=
  K.moduleCatHomologyClass (CochainComplex.next ℕ n) ((e n).inv.hom ∘ₗ (Z n).subtype)
    fun z ↦ (hZ n z.1).1 z.2

/-- The class of a cocycle is the homology class of the cocycle transported into the complex. -/
lemma moduleCatCohomologyClassOfIso_apply (n : ℕ) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z =
      K.homologyπ n (K.moduleCatCyclesMk ((e n).inv z.1) (n + 1) (CochainComplex.next ℕ n)
        ((hZ n z.1).1 z.2)) :=
  (rfl)

/-- The class of a cocycle `z` is the homology class of any cycle whose underlying element
corresponds to `z` under the identification of the term. -/
lemma moduleCatCohomologyClassOfIso_eq_homologyπ {n : ℕ} (z : Z n) (y : K.cycles n)
    (hy : (e n).hom (K.iCycles n y) = z.1) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = K.homologyπ n y := by
  rw [moduleCatCohomologyClassOfIso_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [iCycles_moduleCatCyclesMk, ← hy, Iso.hom_inv_id_apply]

/-- Every cohomology class of a cochain complex of modules is represented by a cocycle. -/
lemma moduleCatCohomologyClassOfIso_surjective (n : ℕ) :
    Function.Surjective (K.moduleCatCohomologyClassOfIso V Z e hZ n) :=
  K.moduleCatHomologyClass_surjective _ _ _ fun x hx ↦
    ⟨⟨(e n).hom x, (hZ n _).2 (by rwa [Iso.hom_inv_id_apply])⟩, Iso.hom_inv_id_apply (e n) x⟩

/-- A cocycle has zero class exactly when its underlying element is in the image of the incoming
differential from the degree preceding it. -/
lemma moduleCatCohomologyClassOfIso_eq_zero_iff_exists {n m : ℕ}
    (hm : (ComplexShape.up ℕ).prev n = m) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = 0 ↔
      ∃ y, K.d m n y = (e n).inv z.1 :=
  K.moduleCatHomologyClass_eq_zero_iff _ _ _ hm z

include hB

/-- The class of a cocycle is zero exactly when its underlying element is a coboundary. -/
lemma moduleCatCohomologyClassOfIso_eq_zero_iff (n : ℕ) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = 0 ↔ z.1 ∈ B n := by
  rw [K.moduleCatCohomologyClassOfIso_eq_zero_iff_exists V Z e hZ rfl]
  exact (hB n z.1).symm

/-- Two cocycles represent the same cohomology class exactly when their difference is a
coboundary. -/
lemma moduleCatCohomologyClassOfIso_eq_iff (n : ℕ) (z w : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z =
        K.moduleCatCohomologyClassOfIso V Z e hZ n w ↔ (z - w).1 ∈ B n := by
  rw [← sub_eq_zero, ← map_sub, moduleCatCohomologyClassOfIso_eq_zero_iff K V Z B e hZ hB]

end CochainPresentation

variable {n} in
/-- Every degree-`n` homology class of a complex of modules is the class of an element killed by
the differential out of degree `n`. -/
lemma exists_homologyπ_moduleCatCyclesMk_eq (m : ι) (hm : c.next n = m) (z : K.homology n) :
    ∃ (x : K.X n) (hx : K.d n m x = 0), K.homologyπ n (K.moduleCatCyclesMk x m hm hx) = z := by
  obtain ⟨z, rfl⟩ := K.moduleCat_homologyπ_surjective n z
  have hz : K.d n m (K.iCycles n z) = 0 := K.moduleCat_d_iCycles_apply n m z
  exact ⟨_, hz,
    congrArg _ (K.moduleCat_iCycles_injective n (iCycles_moduleCatCyclesMk _ _ _ _ _ _))⟩

variable {n} in
/-- If the degree-`n` homology of a complex of modules is finitely generated, there are finitely
many cycles `v i` of degree `n` such that every cycle of degree `n` is a linear combination of
them up to a boundary, the image of an element of the term of degree `p = c.prev n`. -/
lemma exists_fin_moduleCat_cycles_generating (hK : Module.Finite R (K.homology n)) {p : ι}
    (hp : c.prev n = p) :
    ∃ (m : ℕ) (v : Fin m → K.X n), (∀ i l, K.d n l (v i) = 0) ∧
      ∀ x : K.X n, (∀ l, K.d n l x = 0) →
        ∃ (r : Fin m → R) (y : K.X p), ∑ i, r i • v i + K.d p n y = x := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := K.homology n)
  choose w hw using fun i ↦ K.moduleCat_homologyπ_surjective n (s i)
  refine ⟨m, fun i ↦ K.iCycles n (w i), fun i l ↦ ?_, fun x hx ↦ ?_⟩
  · exact K.moduleCat_d_iCycles_apply n l (w i)
  · set x' := K.moduleCatCyclesMk x _ rfl (hx _)
    have hmem : K.homologyπ n x' ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Submodule.mem_span_range_iff_exists_fun R |>.1 hmem
    have h0 : K.homologyπ n (x' - ∑ i, r i • w i) = 0 := by
      simp [map_sub, map_sum, map_smul, hw, hr]
    obtain ⟨y, hy⟩ := (K.moduleCat_homologyπ_eq_zero_iff hp _).1 h0
    refine ⟨r, y, ?_⟩
    have hy' := congrArg (K.iCycles n) hy
    rw [moduleCat_iCycles_toCycles_apply] at hy'
    rw [hy', map_sub, map_sum, HomologicalComplex.iCycles_moduleCatCyclesMk]
    simp

variable {n} in
/-- A finite sum of cycles built by `moduleCatCyclesMk` is the cycle built from the sum. -/
lemma sum_moduleCatCyclesMk {κ : Type*} (s : Finset κ) (x : κ → K.X n) (m : ι)
    (hm : c.next n = m) (hx : ∀ i, K.d n m (x i) = 0) :
    ∑ i ∈ s, K.moduleCatCyclesMk (x i) m hm (hx i) =
      K.moduleCatCyclesMk (∑ i ∈ s, x i) m hm
        (by rw [map_sum]; exact Finset.sum_eq_zero fun i _ ↦ hx i) :=
  K.moduleCat_iCycles_injective n (by simp only [map_sum, iCycles_moduleCatCyclesMk])

variable {n} in
/-- Two degree-`n` cycles of a complex of modules whose difference is a boundary have the same
homology class. -/
lemma moduleCat_homologyπ_eq_of_iCycles_sub_eq_d {z w : K.cycles n} {m : ι} (b : K.X m)
    (h : K.iCycles n z - K.iCycles n w = K.d m n b) : K.homologyπ n z = K.homologyπ n w := by
  have hb : z - w = K.toCycles m n b := K.moduleCat_iCycles_injective n <| by
    rw [map_sub, h, moduleCat_iCycles_toCycles_apply]
  rw [← sub_eq_zero, ← map_sub, hb, ← ModuleCat.comp_apply, toCycles_comp_homologyπ]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

variable {K} in
/-- **Homology classes of a union of subcomplexes.** Let `φ i : L i ⟶ K` be chain maps of
complexes of modules that are injective in degree `c.next n`, and suppose every element of `K.X n`
comes from some `L i`. Then every degree-`n` homology class of `K` comes from some `L i`. -/
theorem exists_homologyMap_eq_of_injective {κ : Type*}
    {L : κ → HomologicalComplex (ModuleCat R) c} (φ : ∀ i, L i ⟶ K)
    (hφ : ∀ i, Function.Injective ((φ i).f (c.next n)))
    (h : ∀ x : K.X n, ∃ i y, (φ i).f n y = x) (z : K.homology n) :
    ∃ i y, homologyMap (φ i) n y = z := by
  obtain ⟨z, rfl⟩ := K.moduleCat_homologyπ_surjective n z
  obtain ⟨i, y, hy⟩ := h (K.iCycles n z)
  -- the lift `y` of the cycle is again a cycle, since its differential maps to zero injectively
  have hdy : (L i).d n (c.next n) y = 0 := hφ i <| by
    rw [← Hom.comm_apply, hy, map_zero, K.moduleCat_d_iCycles_apply]
  refine ⟨i, (L i).homologyπ n ((L i).moduleCatCyclesMk y _ rfl hdy), ?_⟩
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply K.moduleCat_iCycles_injective
  rw [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk, hy]

variable {K} in
/-- **Vanishing of homology classes in a union of subcomplexes.** Let `φ j : L j ⟶ K` be chain maps
of complexes of modules that are injective in degree `n`, and let `ψ j : L i ⟶ L j` be chain maps
compatible with them, defined for the indices `j` satisfying `P j`. Suppose every element of the
term of degree `c.prev n` of `K` comes from some `L j` with `P j`. Then a degree-`n` homology class
of `L i` that vanishes in `K` already vanishes in some `L j` with `P j`. -/
theorem exists_homologyMap_eq_zero_of_injective {κ : Type*}
    {L : κ → HomologicalComplex (ModuleCat R) c} (φ : ∀ j, L j ⟶ K)
    (hφ : ∀ j, Function.Injective ((φ j).f n)) {m : ι} (hm : c.prev n = m) {i : κ}
    {P : κ → Prop} (ψ : ∀ j, P j → (L i ⟶ L j)) (hψ : ∀ j hj, ψ j hj ≫ φ j = φ i)
    (h : ∀ x : K.X m, ∃ j, ∃ _ : P j, ∃ y, (φ j).f m y = x) (y : (L i).homology n)
    (hy : homologyMap (φ i) n y = 0) : ∃ j, ∃ hj : P j, homologyMap (ψ j hj) n y = 0 := by
  obtain ⟨z, rfl⟩ := (L i).moduleCat_homologyπ_surjective n y
  -- the image of the cycle `z` in `K` is the boundary of some `w`
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply,
    K.moduleCat_homologyπ_eq_zero_iff hm] at hy
  obtain ⟨w, hw⟩ := hy
  -- `w` comes from some `L j`, where its lift bounds the image of `z`
  obtain ⟨j, hj, w', rfl⟩ := h w
  refine ⟨j, hj, ?_⟩
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply,
    (L j).moduleCat_homologyπ_eq_zero_iff hm]
  refine ⟨w', (L j).moduleCat_iCycles_injective n (hφ j ?_)⟩
  -- push both cycles into `K`: naturality of the differential, then `hw` and compatibility `hψ`
  calc (φ j).f n ((L j).iCycles n ((L j).toCycles m n w'))
      = (φ j).f n ((L j).d m n w') := by
        rw [moduleCat_iCycles_toCycles_apply]
    _ = K.d m n ((φ j).f m w') := (Hom.comm_apply _ _ _ _).symm
    _ = K.iCycles n (K.toCycles m n ((φ j).f m w')) :=
      (moduleCat_iCycles_toCycles_apply _ _ _ _).symm
    _ = (φ i).f n ((L i).iCycles n z) := by
        rw [hw, moduleCat_iCycles_cyclesMap_apply]
    _ = (φ j).f n ((L j).iCycles n (cyclesMap (ψ j hj) n z)) := by
      rw [moduleCat_iCycles_cyclesMap_apply, ← ModuleCat.comp_apply ((ψ j hj).f n), ← comp_f, hψ]

variable {K} in
/-- A chain map of complexes of modules sends the class of a cycle to the class of its image. -/
lemma homologyMap_homologyπ_moduleCatCyclesMk {L : HomologicalComplex (ModuleCat R) c}
    (φ : K ⟶ L) {n : ι} (x : K.X n) (m : ι) (hm : c.next n = m) (hx : K.d n m x = 0) :
    (homologyMap φ n).hom ((K.homologyπ n).hom (K.moduleCatCyclesMk x m hm hx)) =
      (L.homologyπ n).hom (L.moduleCatCyclesMk ((φ.f n).hom x) m hm
        (by rw [Hom.comm_apply, hx, map_zero])) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, homologyπ_naturality, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  congr 1
  apply L.moduleCat_iCycles_injective
  rw [moduleCat_iCycles_cyclesMap_apply, iCycles_moduleCatCyclesMk, iCycles_moduleCatCyclesMk]

/-- **Local nilpotence passes to homology.** Let `φ` be a family of chain endomorphisms of a
complex of modules. If every element of the degree-`n` term is killed by all sufficiently long
composites of the maps `(φ i).f n`, then every degree-`n` homology class is killed by all
sufficiently long composites of the induced maps `homologyMap (φ i) n`. -/
theorem iSup_wordKer_homologyMap_eq_top {κ : Type*} (φ : κ → (K ⟶ K))
    (h : ⨆ d, Module.End.wordKer (fun i ↦ ((φ i).f n).hom) d = ⊤) :
    ⨆ d, Module.End.wordKer (fun i ↦ (homologyMap (φ i) n).hom) d = ⊤ := by
  -- The cycles form a submodule of `K.X n` on which the maps `(φ i).f n` restrict to
  -- `cyclesMap (φ i) n`, and the homology is a quotient of the cycles.
  refine Module.End.iSup_wordKer_eq_top_of_surjective (f := fun i ↦ (cyclesMap (φ i) n).hom)
    (fun i ↦ by rw [← ModuleCat.hom_comp, ← homologyπ_naturality, ModuleCat.hom_comp])
    (K.moduleCat_homologyπ_surjective n) ?_
  exact Module.End.iSup_wordKer_eq_top_of_injective
    (fun i ↦ by rw [← ModuleCat.hom_comp, cyclesMap_i, ModuleCat.hom_comp])
    (K.moduleCat_iCycles_injective n) h

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat R) c)} (hS : S.ShortExact)

/-- **The connecting map of a short exact sequence of complexes of modules, on classes.** Let `z₃`
be a cycle of `S.X₃` in degree `i`, `x₂` an element of `S.X₂` in degree `i` lifting it, and `z₁` a
cycle of `S.X₁` in degree `j` whose image in `S.X₂` is the differential of `x₂`.  Then the
connecting map sends the class of `z₃` to the class of `z₁`. -/
theorem moduleCat_δ_homologyπ (i j : ι) (hij : c.Rel i j) (z₃ : S.X₃.cycles i) (x₂ : S.X₂.X i)
    (hx₂ : (S.g.f i).hom x₂ = (S.X₃.iCycles i).hom z₃) (z₁ : S.X₁.cycles j)
    (hz₁ : (S.f.f j).hom ((S.X₁.iCycles j).hom z₁) = (S.X₂.d i j).hom x₂) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom z₃) = (S.X₁.homologyπ j).hom z₁ := by
  have hd₃ : (S.X₃.d i j).hom ((S.X₃.iCycles i).hom z₃) = 0 := by
    exact S.X₃.moduleCat_d_iCycles_apply i j z₃
  -- Mathlib's computation of the connecting map, for the cycle `iCycles z₃` and the lift `x₂`.
  have key := hS.δ_apply i j hij ((S.X₃.iCycles i).hom z₃) hd₃ x₂ hx₂
    ((S.X₁.iCycles j).hom z₁) hz₁ (c.next j) rfl
  -- The cycles built by `cyclesMk` from `iCycles z₃` and `iCycles z₁` are `z₃` and `z₁`.
  have h₃ : S.X₃.cyclesMk ((S.X₃.iCycles i).hom z₃) j (c.next_eq' hij) hd₃ = z₃ :=
    S.X₃.moduleCat_iCycles_injective i
      (HomologicalComplex.i_cyclesMk (C := ModuleCat R) S.X₃ _ j (c.next_eq' hij) hd₃)
  have h₁ : S.X₁.cyclesMk ((S.X₁.iCycles j).hom z₁) (c.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j x₂ _ hz₁ _) = z₁ :=
    S.X₁.moduleCat_iCycles_injective j
      (HomologicalComplex.i_cyclesMk (C := ModuleCat R) S.X₁ _ (c.next j) rfl _)
  rw [h₃, h₁] at key
  exact key

/-- **Lifting a class along a prescribed boundary.** Let `x₃` be a degree-`i` homology class of
`S.X₃` and `z₁` a degree-`j` cycle of `S.X₁` whose class is the image of `x₃` under the connecting
map. Then some element `x₂` of `S.X₂` in degree `i` has differential the image of `z₁`, and maps
onto a cycle of `S.X₃` representing `x₃`. This is the converse of `moduleCat_δ_homologyπ`: the
boundary of the lift is prescribed on the nose, not only up to a boundary. -/
theorem moduleCat_exists_d_eq_of_δ_eq (i j : ι) (hij : c.Rel i j) (x₃ : S.X₃.homology i)
    (z₁ : S.X₁.cycles j) (h : (hS.δ i j hij).hom x₃ = (S.X₁.homologyπ j).hom z₁) :
    ∃ (x₂ : S.X₂.X i) (z₃ : S.X₃.cycles i),
      (S.X₂.d i j).hom x₂ = (S.f.f j).hom ((S.X₁.iCycles j).hom z₁) ∧
        (S.g.f i).hom x₂ = (S.X₃.iCycles i).hom z₃ ∧ (S.X₃.homologyπ i).hom z₃ = x₃ := by
  have hSi := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i
  have hSj := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS j
  have : Epi (S.g.f i) := hSi.epi_g
  have : Mono (S.f.f j) := hSj.mono_f
  -- Represent `x₃` by a cycle `z₃` and lift it to `y₂` in `S.X₂`.
  obtain ⟨z₃, rfl⟩ := S.X₃.moduleCat_homologyπ_surjective i x₃
  obtain ⟨y₂, hy₂⟩ := (ModuleCat.epi_iff_surjective (S.g.f i)).1 inferInstance
    ((S.X₃.iCycles i).hom z₃)
  -- The differential of `y₂` dies in `S.X₃`, so it comes from an element `y₁` of `S.X₁`.
  have hdy₂ : (S.g.f j).hom ((S.X₂.d i j).hom y₂) = 0 := by
    rw [← HomologicalComplex.Hom.comm_apply, hy₂, ← ModuleCat.comp_apply,
      HomologicalComplex.iCycles_d]
    simp
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : S.X₁.X j, (S.f.f j).hom y₁ = (S.X₂.d i j).hom y₂ :=
    (ShortComplex.moduleCat_exact_iff _).1 hSj.exact _ hdy₂
  have hdy₁ : (S.X₁.d j (c.next j)).hom y₁ = 0 :=
    hS.d_eq_zero_of_f_eq_d_apply i j y₂ y₁ hy₁ _
  -- By `moduleCat_δ_homologyπ`, `z₁` and `y₁` are homologous: `z₁ - y₁ = d b`.
  have hδ := hS.moduleCat_δ_homologyπ i j hij z₃ y₂ hy₂
    (S.X₁.moduleCatCyclesMk y₁ (c.next j) rfl hdy₁)
    (by rw [HomologicalComplex.iCycles_moduleCatCyclesMk]; exact hy₁)
  rw [h] at hδ
  obtain ⟨b, hb'⟩ := (S.X₁.moduleCat_homologyπ_eq_iff (c.prev_eq' hij) _ _).1 hδ
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk] at hb'
  -- Correct the lift by the image of `b`.
  refine ⟨y₂ + (S.f.f i).hom b, z₃, ?_, ?_, rfl⟩
  · rw [map_add, ← hy₁, HomologicalComplex.Hom.comm_apply, hb', map_sub, add_sub_cancel]
  · rw [map_add, hy₂, ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, S.zero]
    simp

include hS in
/-- **Lifts along a prescribed boundary are unique up to boundaries and cycles of `S.X₁`.** Let
`x₂, x₂'` be elements of `S.X₂` in degree `i` with the same differential, whose images in `S.X₃`
are homologous cycles. Then `x₂ - x₂'` is the sum of a boundary and the image of an element `a`
of `S.X₁` killed by the differential to degree `j` (so a cycle when `c.Rel i j`). -/
theorem moduleCat_exists_sub_eq_d_add (i j p : ι) (hp : c.prev i = p)
    (x₂ x₂' : S.X₂.X i) (hd : (S.X₂.d i j).hom x₂ = (S.X₂.d i j).hom x₂')
    (z₃ z₃' : S.X₃.cycles i) (hx₂ : (S.g.f i).hom x₂ = (S.X₃.iCycles i).hom z₃)
    (hx₂' : (S.g.f i).hom x₂' = (S.X₃.iCycles i).hom z₃')
    (hz : (S.X₃.homologyπ i).hom z₃ = (S.X₃.homologyπ i).hom z₃') :
    ∃ (b : S.X₂.X p) (a : S.X₁.X i), (S.X₁.d i j).hom a = 0 ∧
      x₂ - x₂' = (S.X₂.d p i).hom b + (S.f.f i).hom a := by
  have hSi := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i
  have hSj := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS j
  have hSp := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS p
  have : Epi (S.g.f p) := hSp.epi_g
  have : Mono (S.f.f j) := hSj.mono_f
  -- The cycles `z₃` and `z₃'` differ by the boundary of some `b₃`, which lifts to `b`.
  obtain ⟨b₃, hdb⟩ := (S.X₃.moduleCat_homologyπ_eq_iff hp _ _).1 hz
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (S.g.f p)).1 inferInstance b₃
  -- Then `x₂ - x₂' - d b` dies in `S.X₃`, so it is the image of some `a`.
  have hker : (S.g.f i).hom (x₂ - x₂' - (S.X₂.d p i).hom b) = 0 := by
    rw [map_sub, map_sub, hx₂, hx₂', ← HomologicalComplex.Hom.comm_apply, hdb, sub_self]
  obtain ⟨a, ha⟩ : ∃ a : S.X₁.X i, (S.f.f i).hom a = x₂ - x₂' - (S.X₂.d p i).hom b :=
    (ShortComplex.moduleCat_exact_iff _).1 hSi.exact _ hker
  refine ⟨b, a, ?_, ?_⟩
  · -- The image of `d a` is `d (x₂ - x₂' - d b) = 0`, and `S.f` is injective.
    apply (ModuleCat.mono_iff_injective (S.f.f j)).1 inferInstance
    rw [← HomologicalComplex.Hom.comm_apply, ha, map_sub, map_sub, hd, sub_self,
      HomologicalComplex.d_comp_d_apply, sub_zero, map_zero]
  · rw [ha]
    abel

end CategoryTheory.ShortComplex.ShortExact

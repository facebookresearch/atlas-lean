/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
public import MathlibExt.Algebra.Homology.GradedMixedCochainModels

/-!
# Actual DG-category Hochschild trace and completed negative cyclic models

The total Hochschild term is the direct sum of the actual cyclic bar
terms in degree r+n. Its differential is (-1)^n d_internal plus the
alternating composition faces. Connes B is (1-t)sN on those same actual
words, where t is signed cyclic rotation and s inserts the DG identity.

Negative cyclic uses the full product [[u]], not polynomial ordinary
cyclic homology or a periodic quotient. Every model and functor map is
fixed on the actual bar/product components. Over the source base field
this cyclic bar is the derived Hochschild trace A tensor_Ae^L A.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, §2.1 and §3.2;
Loday, Cyclic homology, §1.1. The native DG/cochain primitives retain
their source author/license attribution in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.DGCategoryTraceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology.DGCategoryCyclicBarModels
open MathlibExt.Algebra.Homology.DGCyclicMixedModels
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k]

/-- The actual bar-degree n summand of cohomological Hochschild degree r. -/
abbrev TraceSummand (C : DGCat k) (r : ℤ) (n : ℕ) : Type u :=
  (barTerm C n).X (r + (n : ℤ))

/-- Literal finite-support bar totalization, with every object-cycle summand retained. -/
abbrev TraceValues (C : DGCat k) (r : ℤ) := DirectSum ℕ (TraceSummand C r)

/-- The native bar-degree inclusion in the total trace. -/
def includeTrace (C : DGCat k) (r : ℤ) (n : ℕ) :
    TraceSummand C r n →ₗ[k] TraceValues C r := DirectSum.lof k ℕ (TraceSummand C r) n

/-- The internal cochain differential on the same bar-degree summand. -/
def traceInternalBlock (C : DGCat k) (r : ℤ) (n : ℕ) :
    TraceSummand C r n →ₗ[k] TraceValues C (r + 1) :=
  (includeTrace C (r + 1) n).comp
    ((degreeCast (barTerm C n) (by omega)).comp
      ((barTerm C n).d (r + (n : ℤ)) (r + (n : ℤ) + 1)).hom)

/-- The actual alternating adjacent-composition faces of the cyclic Hom words. -/
def traceFaceBlock (C : DGCat k) (r : ℤ) : (n : ℕ) →
    (TraceSummand C r n →ₗ[k] TraceValues C (r + 1))
  | 0 => 0
  | n + 1 => (includeTrace C (r + 1) n).comp
      ((degreeCast (barTerm C n) (by omega)).comp
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          ((face C n i).f (r + ((n + 1 : ℕ) : ℤ))).hom))

/-- Every total differential is fixed on every actual bar generator. -/
def traceDifferential (C : DGCat k) (r : ℤ) : TraceValues C r →ₗ[k] TraceValues C (r + 1) :=
  DirectSum.toModule k ℕ (TraceValues C (r + 1))
    (fun n => (-1 : ℤ) ^ n • traceInternalBlock C r n + traceFaceBlock C r n)

/-- The actual bar-total cochain complex has all terms and differentials fixed. -/
structure TraceTotalModel (C : DGCat k) where
  complex : Cochains k
  termIso : ∀ r : ℤ, complex.X r ≅ ModuleCat.of k (TraceValues C r)
  differential_eq : ∀ r : ℤ,
    complex.d r (r + 1) ≫ (termIso (r + 1)).hom =
      (termIso r).hom ≫ ModuleCat.ofHom (traceDifferential C r)

/-- The cyclic-complex sign is separate from the native Koszul word braiding. -/
def signedRotation (C : DGCat k) (n : ℕ) : barTerm C n ⟶ barTerm C n :=
  (-1 : ℤ) ^ n • rotation C n

/-- Powers of the actual signed cyclic operator. -/
def signedRotationPower (C : DGCat k) (n : ℕ) : ℕ → (barTerm C n ⟶ barTerm C n)
  | 0 => 𝟙 _
  | i + 1 => signedRotationPower C n i ≫ signedRotation C n

/-- The literal cyclic norm 1+t+...+t^n. -/
def cyclicNorm (C : DGCat k) (n : ℕ) : barTerm C n ⟶ barTerm C n :=
  ∑ i ∈ Finset.range (n + 1), signedRotationPower C n i

/-- The actual chain Connes operator, with native identity insertion and rotation. -/
def connesBar (C : DGCat k) (n : ℕ) : barTerm C n ⟶ barTerm C (n + 1) :=
  cyclicNorm C n ≫ extraDegeneracy C n ≫ (𝟙 _ - signedRotation C (n + 1))

/-- The total Connes map has cohomological degree -1 on every bar summand. -/
def connesDifferential (C : DGCat k) (r : ℤ) : TraceValues C r →ₗ[k] TraceValues C (r - 1) :=
  DirectSum.toModule k ℕ (TraceValues C (r - 1)) (fun n =>
    (includeTrace C (r - 1) (n + 1)).comp
      ((degreeCast (barTerm C (n + 1)) (by omega)).comp
        ((connesBar C n).f (r + (n : ℤ))).hom))

/-- The mixed trace uses exactly the actual Connes map and cyclic bar total. -/
structure TraceMixedModel (C : DGCat k) where
  total : TraceTotalModel C
  connes : Cochain total.complex total.complex (-1)
  connes_eq : ∀ r : ℤ,
    connes.v r (r - 1) (by omega) ≫ (total.termIso (r - 1)).hom =
      (total.termIso r).hom ≫ ModuleCat.ofHom (connesDifferential C r)
  closed : δ (-1) 0 connes = 0
  square : connes.comp connes (show (-1 : ℤ) + (-1) = -2 from rfl) = 0

/-- The source's unweighted mixed trace has this same complex and Connes map at every weight. -/
def mixedTrace {C : DGCat k} (M : TraceMixedModel C) : GradedMixed k where
  weight _ := M.total.complex
  epsilon _ := M.connes
  closed _ := M.closed
  square _ := M.square

/-- The completed product [[u]] uses precisely the fixed trace mixed object. -/
abbrev NegativeTraceModel {C : DGCat k} (M : TraceMixedModel C) :=
  NegativeCyclicModel (mixedTrace M) 0

/-- The literal u^0 coefficient forgets the completed higher negative-cyclic powers. -/
def coefficientZero {C : DGCat k} (M : TraceMixedModel C) (r : ℤ) :
    term (mixedTrace M) 0 r ⟶ M.total.complex.X r :=
  ModuleCat.ofHom
    { toFun := fun a => degreeCast M.total.complex (by omega : r - 2 * (0 : ℤ) = r) (a 0)
      map_add' := by intro a b; simp only [Pi.add_apply, map_add]
      map_smul' := by intro a b; simp only [Pi.smul_apply, map_smul, RingHom.id_apply] }

/-- The source forgetful map is fixed by the native u^0 projection in every degree.
Assembling these components as a cochain map is a separate construction request. -/
structure NegativeProjectionModel {C : DGCat k} {M : TraceMixedModel C}
    (N : NegativeTraceModel M) where
  map : N.complex ⟶ M.total.complex
  normalized : ∀ r : ℤ, map.f r = (N.termIso r).hom ≫ coefficientZero M r

/-- The native DG functor maps each bar-degree summand without dropping object cycles. -/
def traceTermMap {C D : DGCat k} (F : C ⟶ D) (r : ℤ) :
    TraceValues C r →ₗ[k] TraceValues D r :=
  DirectSum.toModule k ℕ (TraceValues D r) (fun n =>
    (includeTrace D r n).comp ((barMap F n).f (r + (n : ℤ))).hom)

/-- A trace cochain map is fixed on all bars and commutes with the same actual Connes map. -/
structure TraceMapModel {C D : DGCat k} (F : C ⟶ D)
    (M : TraceMixedModel C) (N : TraceMixedModel D) where
  map : M.total.complex ⟶ N.total.complex
  term_eq : ∀ r : ℤ,
    map.f r ≫ (N.total.termIso r).hom =
      (M.total.termIso r).hom ≫ ModuleCat.ofHom (traceTermMap F r)
  connes_comm : ∀ (a b : ℤ) (h : a + (-1 : ℤ) = b),
    map.f a ≫ N.connes.v a b h = M.connes.v a b h ≫ map.f b

/-- The normalized trace map is the actual constant-weight mixed map. -/
def traceMixedMap {C D : DGCat k} {F : C ⟶ D}
    {M : TraceMixedModel C} {N : TraceMixedModel D} (f : TraceMapModel F M N) :
    MixedMap (mixedTrace M) (mixedTrace N) where
  map _ := f.map
  epsilon _ a b h := (f.connes_comm a b h).symm

/-- The negative-cyclic map is fixed on every actual [[u]] coefficient. -/
structure NegativeTraceMapModel {C D : DGCat k} {F : C ⟶ D}
    {M : TraceMixedModel C} {N : TraceMixedModel D} (f : TraceMapModel F M N)
    (P : NegativeTraceModel M) (Q : NegativeTraceModel N) where
  map : P.complex ⟶ Q.complex
  normalized : IsNegativeCyclicMap (traceMixedMap f) 0 P Q map

/-- A genuine negative-cyclic functor retains its actual bar/product models and all map formulas. -/
structure NegativeTraceSystem (k : Type u) [CommRing k] where
  mixed : ∀ C : DGCat k, TraceMixedModel C
  traceMap : ∀ {C D : DGCat k} (F : C ⟶ D), TraceMapModel F (mixed C) (mixed D)
  negative : ∀ C : DGCat k, NegativeTraceModel (mixed C)
  map : ∀ {C D : DGCat k} (F : C ⟶ D),
    NegativeTraceMapModel (traceMap F) (negative C) (negative D)
  map_id : ∀ C : DGCat k, (map (𝟙 C)).map = 𝟙 (negative C).complex
  map_comp : ∀ {C D E : DGCat k} (f : C ⟶ D) (g : D ⟶ E),
    (map (f ≫ g)).map = (map f).map ≫ (map g).map

/-- The literal source negative-cyclic functor on actual DG functors. -/
def negativeTraceFunctor (S : NegativeTraceSystem k) : DGCat k ⥤ Cochains k where
  obj C := (S.negative C).complex
  map F := (S.map F).map
  map_id := S.map_id
  map_comp := S.map_comp

end MathlibExt.Algebra.Homology.DGCategoryTraceModels

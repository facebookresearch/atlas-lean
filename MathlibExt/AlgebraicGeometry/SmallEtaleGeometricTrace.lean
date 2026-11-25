/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Length

/-!
# Actual geometric Tate stalks and finite-flat coefficient trace

Stalks are Mathlib's actual small-étale geometric point fibres.
Their coordinates are pinned on every colimit insertion of actual
Kummer-root words evaluated at the actual lift to an algebraically
closed field. A finite-flat trace is fixed at all geometric stalks
by the sum over actual scheme lifts, weighted by the actual
Artin local-ring lengths of the geometric fibre.

This handles inseparable finite field extensions by their fibre lengths,
and never supplies an arbitrary corestriction or numerical trace.
Generic geometric-stalk and weighted-trace proofs are source-complete
integration from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/EtaleCohomology/WeightedTrace/WeightedTraceTransport.lean,
and KummerTheory (Apache 2.0). Native points/filtered colimits are reused.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
open MathlibExt.AlgebraicGeometry.SmallEtaleKummerFunctoriality
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open scoped TensorProduct BigOperators

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

variable {l : ℕ} (S : Data l)

/-- Actual word of roots in the recursive sheafified Tate tensor coefficient. -/
def tateWord (X : Scheme.{0}) (U : X.Etaleᵒᵖ) :
    (j : ℕ) → (Fin j → (rootsSheaf X (S.gm X) l).obj.obj U) →
      (S.coefficient X j).obj.obj U
  | 0, _ =>
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Scalar (FiniteCoefficient l)))).app U)
          (1 : FiniteCoefficient l)
  | 1, a => a 0
  | j+2, a =>
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
        ((S.coefficient X (j+1)).obj ⊗ (rootsSheaf X (S.gm X) l).obj)).app U)
          ((tateWord X U (j+1) (fun i => a i.castSucc)) ⊗ₜ[Scalar] a (Fin.last (j+1)))

abbrev GeometricLift {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (p : Spec (.of Ω) ⟶ X) (U : X.Etale) :=
  Over.mk p ⟶ (Scheme.Etale.forget X).obj U

abbrev stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (F : Coefficients X) : ModuleCat.{1} Scalar :=
  (Scheme.pointSmallEtale p).sheafFiber.obj F

/-- Actual colimit insertion of a section through its actual geometric lift. -/
def stalkSection {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (F : Coefficients X) (U : X.Etale)
    (t : GeometricLift p U) (a : F.obj.obj (op U)) : stalk p F :=
  ((Scheme.pointSmallEtale p).toPresheafFiber U t F.obj).hom a

/-- The actual root unit before evaluating on a geometric lift. -/
def rootUnit {X : Scheme.{0}} (U : X.Etale)
    (a : (rootsSheaf X (S.gm X) l).obj.obj (op U)) : (Γ(U.left,⊤))ˣ :=
  (((kernel.ι (powerMap X (S.gm X) l)).hom.app (op U) a).down).toMul

def geometricRootValue {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (p : Spec (.of Ω) ⟶ X) (U : X.Etale) (t : GeometricLift p U)
    (a : (rootsSheaf X (S.gm X) l).obj.obj (op U)) : Ωˣ :=
  Units.map (((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.left.appTop.hom).toMonoidHom)
    (rootUnit S U a)

/-- Coordinates on the geometric stalks of the Tate twists, normalized by a unit $\zeta$: for a
geometric point $p : \operatorname{Spec} \Omega \to X$ ($\Omega$ algebraically closed) and
$\zeta \in \Omega^\times$, isomorphisms from the stalks at $p$ of the Tate twists
$\mu_l^{\otimes j}$ of the cohomology data `S` (`S.coefficient X j`, $j \ge 0$, with
$\mu_l^{\otimes 0} = \mathbb{Z}/l$) to $\mathbb{Z}/l$, such that for every étale $U \to X$, lift
$t$ of $p$ to $U$, sections $a_1, \dots, a_j$ of $\mu_l$ over $U$ and integers $r_1, \dots, r_j$
with $a_i(t) = \zeta^{r_i}$ in $\Omega^\times$ for all $i$, the germ at $t$ of the tensor
$a_1 \otimes \dots \otimes a_j$ (`tateWord`; the unit section for $j = 0$) is sent to
$r_1 \cdots r_j \bmod l$. -/
structure TateCoordinates {X : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (ζ : Ωˣ) where
  comparison : ∀ j : ℕ, stalk p (S.coefficient X j) ≅ ModuleCat.of Scalar (FiniteCoefficient l)
  word : ∀ (j : ℕ) (U : X.Etale) (t : GeometricLift p U)
    (a : Fin j → (rootsSheaf X (S.gm X) l).obj.obj (op U)) (r : Fin j → ℤ),
    (∀ i, geometricRootValue S p U t (a i) = ζ ^ (r i)) →
    (comparison j).hom (stalkSection p (S.coefficient X j) U t (tateWord S X (op U) j a)) =
      ULift.up (∏ i, (r i : ZMod l))

abbrev Lifts {Y X : Scheme.{0}} (f : Y ⟶ X) {Ω : Type} [Field Ω]
    (p : Spec (.of Ω) ⟶ X) := {s : Spec (.of Ω) ⟶ Y // s ≫ f = p}

/-- The lift to the actual fibre product, with its actual projection equations. -/
def pulledLift {Y X : Scheme.{0}} (f : Y ⟶ X) {Ω : Type} [Field Ω]
    (p : Spec (.of Ω) ⟶ X) (s : Lifts f p) (U : X.Etale) (t : GeometricLift p U) :
    GeometricLift s.val ((baseChange f).obj U) :=
  Over.homMk (pullback.lift t.left s.val (t.w.trans s.property.symm))
    (by exact pullback.lift_snd _ _ _)

/-- Actual stalk projection, uniquely fixed by all source colimit insertions. -/
structure StalkProjection {Y X : Scheme.{0}} (f : Y ⟶ X) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ X) (s : Lifts f p) (F : Coefficients Y) where
  map : stalk p ((pushforward f).obj F) ⟶ stalk s.val F
  normalized : ∀ (U : X.Etale) (t : GeometricLift p U)
    (a : F.obj.obj (op ((baseChange f).obj U))),
    map (stalkSection p ((pushforward f).obj F) U t a) =
      stalkSection s.val F ((baseChange f).obj U) (pulledLift f p s U t) a

/-- Actual geometric-fibre length, including inseparable multiplicities. The morphism is
finite, so the geometric fibre is a finite scheme over the field and its local rings are
Artinian, of finite length; the conversion to `ℕ` loses nothing. -/
def fibreMultiplicity {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] {Ω : Type} [Field Ω]
    (p : Spec (.of Ω) ⟶ X) (s : Lifts f p) : ℕ := by
  let B := pullback f p
  let b : Spec (.of Ω) ⟶ B := pullback.lift s.val (𝟙 _) (by simpa using s.property)
  let R := B.presheaf.stalk (b default)
  exact (Module.length R R).toNat

/-- Stalk data for the cohomology data `S`, where $\Omega$ ranges over algebraically closed fields:
for every scheme $X$, geometric point $p : \operatorname{Spec} \Omega \to X$ and primitive $l$-th
root of unity $\zeta \in \Omega^\times$, with $l$ invertible in $\Omega$, Tate coordinates at $p$
for $\zeta$ (`TateCoordinates`); for every morphism $f : Y \to X$, geometric point $p$ of $X$, lift
$s$ of $p$ to $Y$ and étale sheaf $F$ on $Y$, a map from the stalk of $f_*F$ at $p$ to the stalk of
$F$ at $s$ sending the germ at a lift $t$ of $p$ to an étale $U \to X$ of each section of $F$ over
$U \times_X Y$ to its germ at the induced lift $(t, s)$ (`StalkProjection`); and, for $f$ finite,
finiteness of the set of lifts of $p$ to $Y$. -/
structure StalkSources where
  coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (ζ : Ωˣ), IsUnit (l : Ω) →
      IsPrimitiveRoot ζ l → TateCoordinates S p ζ
  projection : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (s : Lifts f p) (F : Coefficients Y), StalkProjection f p s F
  finite : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ X), Finite (Lifts f p)

/-- Finite-flat coefficient trace fixed by the actual weighted geometric-fibre sum. The
coefficient prime `l` is invertible on the target (`_hX`), so every geometric point of `X`
has a primitive `l`-th root of unity and the normalization applies at all of them; without
this the condition would not constrain the trace where `l` vanishes. -/
structure CoefficientTrace {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    (P : StalkSources S) (_hX : IsUnit (l : Γ(X, ⊤))) where
  map : ∀ j : ℕ, (pushforward f).obj (S.coefficient Y j) ⟶ S.coefficient X j
  normalized : ∀ (j : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (ζ : Ωˣ) (hu : IsUnit (l : Ω)) (hζ : IsPrimitiveRoot ζ l)
    (a : stalk p ((pushforward f).obj (S.coefficient Y j))),
    letI := P.finite f Ω p
    letI := Fintype.ofFinite (Lifts f p)
    ((P.coordinates X Ω p ζ hu hζ).comparison j).hom
      (((Scheme.pointSmallEtale p).sheafFiber.map (map j)).hom a) =
    ∑ s : Lifts f p, fibreMultiplicity f p s •
      ((P.coordinates Y Ω s.val ζ hu hζ).comparison j).hom
        (((P.projection f Ω p s (S.coefficient Y j)).map).hom a)


/-- Geometric stalk coefficient base change, computed from the actual sheaf map and projection. -/
def stalkBaseChange {l : ℕ} {S : Data l} (P : StalkSources S)
    {Y X : Scheme.{0}} (f : Y ⟶ X) {A : Coefficients X} {B : Coefficients Y}
    (β : A ⟶ (pushforward f).obj B) {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (s : Lifts f p) : stalk p A ⟶ stalk s.val B :=
  (Scheme.pointSmallEtale p).sheafFiber.map β ≫ (P.projection f Ω p s B).map

/-- Generic finite-flat trace normalized by the actual inverse coefficient base change.
This applies equally to positive, negative and other genuine pulled local-system coefficients. -/
structure TraceWithBaseChange {l : ℕ} {S : Data l} (P : StalkSources S)
    {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Flat f]
    (A : Coefficients X) (B : Coefficients Y) (β : A ⟶ (pushforward f).obj B) where
  map : (pushforward f).obj B ⟶ A
  invertible : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (s : Lifts f p), IsIso (stalkBaseChange P f β p s)
  normalized : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (p : Spec (.of Ω) ⟶ X) (a : stalk p ((pushforward f).obj B)),
    letI := P.finite f Ω p
    letI := Fintype.ofFinite (Lifts f p)
    letI := fun s : Lifts f p => invertible Ω p s
    ((Scheme.pointSmallEtale p).sheafFiber.map map).hom a =
    ∑ s : Lifts f p, fibreMultiplicity f p s •
      (inv (stalkBaseChange P f β p s)).hom (((P.projection f Ω p s B).map).hom a)

end MathlibExt.AlgebraicGeometry.SmallEtaleGeometricTrace

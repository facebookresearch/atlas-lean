/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GenericSectionMaps

/-!
# Total spaces characterized by actual pulled-back sections

The total space represents sections of the given module sheaf on every
scheme over its base. Its universal section and every map into the total
space are fixed by the native module pullback and its unit/composition maps.
For locally free modules this is the ordinary vector bundle, with no
properness or restriction to complex schemes.

Source: AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Constructions/VectorBundleOfModule.lean`
(Apache 2.0). The source defines V(E) = Spec Sym(E), representing Hom(E,O).
The section-representing model here uses the source construction on E^vee;
for E = Ω¹ it is Spec Sym(T_X). Construction from a locally free module,
including this native dual identification, is a source-integration request.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralModuleTotalSpaces

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Opposite
open GenericSectionMaps CoherentCurveLinearSeries LineBundleTaskContracts

/-- The native section pulled through a map over the specified base. -/
def pulledSection {X T V : Scheme.{0}} (E : X.Modules) (p : V ⟶ X)
    (s : Γ((Scheme.Modules.pullback p).obj E, ⊤))
    (f : T ⟶ X) (g : T ⟶ V) (h : g ≫ p = f) :
    Γ((Scheme.Modules.pullback f).obj E, ⊤) :=
  (((pullbackSection g (topSectionHom V ((Scheme.Modules.pullback p).obj E) s) ≫
    (Scheme.Modules.pullbackComp g p).hom.app E ≫
      (Scheme.Modules.pullbackCongr h).hom.app E).val.app (op ⊤)).hom
        (1 : Γ(T, ⊤)))

/-- A source-characterized total space. Its universal property includes the
actual section equality, and quantifies over all scheme-valued points. -/
structure TotalSpace (X : Scheme.{0}) (E : X.Modules) where
  total : Scheme.{0}
  projection : total ⟶ X
  universalSection : Γ((Scheme.Modules.pullback projection).obj E, ⊤)
  universal : ∀ (T : Scheme.{0}) (f : T ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj E, ⊤)),
    ∃! g : T ⟶ total, ∃ h : g ≫ projection = f,
      pulledSection E projection universalSection f g h = s

namespace TotalSpace

variable {X : Scheme.{0}} {E : X.Modules} (V : TotalSpace X E)

/-- The map represented by the specified actual pulled-back section. -/
def lift {T : Scheme.{0}} (f : T ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj E, ⊤)) : T ⟶ V.total :=
  Classical.choose (V.universal T f s)

theorem lift_over {T : Scheme.{0}} (f : T ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    V.lift f s ≫ V.projection = f :=
  (Classical.choose_spec (V.universal T f s)).1.choose

theorem lift_section {T : Scheme.{0}} (f : T ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj E, ⊤)) :
    pulledSection E V.projection V.universalSection f (V.lift f s)
      (V.lift_over f s) = s := by
  exact (Classical.choose_spec (V.universal T f s)).1.choose_spec

theorem lift_unique {T : Scheme.{0}} (f : T ⟶ X)
    (s : Γ((Scheme.Modules.pullback f).obj E, ⊤)) (g : T ⟶ V.total)
    (h : g ≫ V.projection = f)
    (hs : pulledSection E V.projection V.universalSection f g h = s) :
    g = V.lift f s :=
  (Classical.choose_spec (V.universal T f s)).2 g ⟨h, hs⟩

/-- The zero section is represented by the actual zero module section. -/
def zero : X ⟶ V.total := V.lift (𝟙 X) 0

@[simp] theorem zero_projection : V.zero ≫ V.projection = 𝟙 X := V.lift_over _ _

end TotalSpace

end MathlibExt.AlgebraicGeometry.GeneralModuleTotalSpaces

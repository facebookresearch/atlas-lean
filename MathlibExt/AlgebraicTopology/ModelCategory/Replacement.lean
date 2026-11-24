/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Functorial cofibrant and fibrant replacements

Restricting a functorial factorization to initial or terminal arrows gives
the chosen replacement functors and their natural trivial-fibration counit
and trivial-cofibration unit. The replacements remain on the original category.

Adapted from the Formal-Math development by Tsutomu Okano and Avocado.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]

section CofibrantReplacement

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- Functorial cofibrant replacement is the intermediate-object functor of
cofibration–trivial-fibration factorization on arrows out of the initial object. -/
noncomputable def cofibrantReplacement : C ⥤ C :=
  ({ obj X := Arrow.mk (initial.to X)
     map f := Arrow.homMk (𝟙 _) f (by simp)
     map_id _ := by ext <;> simp
     map_comp _ _ := by ext <;> simp } : C ⥤ Arrow C) ⋙
    (functorialFactorizationData (cofibrations C) (trivialFibrations C)).Z

/-- The first factor of the initial map. -/
noncomputable def initialToCofibrantReplacement (X : C) :
    (⊥_ C) ⟶ (cofibrantReplacement (C := C)).obj X :=
  (functorialFactorizationData (cofibrations C) (trivialFibrations C)).i.app
    (Arrow.mk (initial.to X))

/-- The natural trivial-fibration counit of cofibrant replacement. -/
noncomputable def cofibrantReplacementCounit : cofibrantReplacement (C := C) ⟶ 𝟭 C where
  app X := (functorialFactorizationData (cofibrations C) (trivialFibrations C)).p.app
    (Arrow.mk (initial.to X))
  naturality X Y f :=
    (functorialFactorizationData (cofibrations C) (trivialFibrations C)).p.naturality
      (Arrow.homMk (f := Arrow.mk (initial.to X)) (g := Arrow.mk (initial.to Y)) (𝟙 _) f)

instance (X : C) : Cofibration (initialToCofibrantReplacement X) :=
  ⟨(functorialFactorizationData (cofibrations C) (trivialFibrations C)).hi _⟩

/-- The two chosen factors compose to the original initial map. -/
lemma cofibrantReplacement_fac (X : C) :
    initialToCofibrantReplacement X ≫ (cofibrantReplacementCounit (C := C)).app X =
      initial.to X :=
  (functorialFactorizationData (cofibrations C) (trivialFibrations C)).fac_app

instance (X : C) : IsCofibrant ((cofibrantReplacement (C := C)).obj X) :=
  (isCofibrant_iff_of_isInitial (initialToCofibrantReplacement X) initialIsInitial).mpr
    inferInstance

instance (X : C) : Fibration ((cofibrantReplacementCounit (C := C)).app X) :=
  ⟨((functorialFactorizationData (cofibrations C) (trivialFibrations C)).hp
    (Arrow.mk (initial.to X))).1⟩

instance (X : C) : WeakEquivalence ((cofibrantReplacementCounit (C := C)).app X) :=
  ⟨((functorialFactorizationData (cofibrations C) (trivialFibrations C)).hp
    (Arrow.mk (initial.to X))).2⟩

end CofibrantReplacement

section FibrantReplacement

variable [HasFunctorialFactorization (trivialCofibrations C) (fibrations C)]

/-- Functorial fibrant replacement is the intermediate-object functor of
trivial-cofibration–fibration factorization on arrows into the terminal object. -/
noncomputable def fibrantReplacement : C ⥤ C :=
  ({ obj X := Arrow.mk (terminal.from X)
     map f := Arrow.homMk f (𝟙 _) (by simp)
     map_id _ := by ext <;> simp
     map_comp _ _ := by ext <;> simp } : C ⥤ Arrow C) ⋙
    (functorialFactorizationData (trivialCofibrations C) (fibrations C)).Z

/-- The natural trivial-cofibration unit of fibrant replacement. -/
noncomputable def fibrantReplacementUnit : (𝟭 C) ⟶ fibrantReplacement (C := C) where
  app X := (functorialFactorizationData (trivialCofibrations C) (fibrations C)).i.app
    (Arrow.mk (terminal.from X))
  naturality X Y f :=
    (functorialFactorizationData (trivialCofibrations C) (fibrations C)).i.naturality
      (Arrow.homMk (f := Arrow.mk (terminal.from X)) (g := Arrow.mk (terminal.from Y)) f (𝟙 _))

/-- The second factor of the terminal map. -/
noncomputable def fibrantReplacementToTerminal (X : C) :
    (fibrantReplacement (C := C)).obj X ⟶ (⊤_ C) :=
  (functorialFactorizationData (trivialCofibrations C) (fibrations C)).p.app
    (Arrow.mk (terminal.from X))

instance (X : C) : Fibration (fibrantReplacementToTerminal X) :=
  ⟨(functorialFactorizationData (trivialCofibrations C) (fibrations C)).hp _⟩

/-- The two chosen factors compose to the original terminal map. -/
lemma fibrantReplacement_fac (X : C) :
    (fibrantReplacementUnit (C := C)).app X ≫ fibrantReplacementToTerminal X =
      terminal.from X :=
  (functorialFactorizationData (trivialCofibrations C) (fibrations C)).fac_app

instance (X : C) : IsFibrant ((fibrantReplacement (C := C)).obj X) :=
  (isFibrant_iff_of_isTerminal (fibrantReplacementToTerminal X) terminalIsTerminal).mpr
    inferInstance

instance (X : C) : Cofibration ((fibrantReplacementUnit (C := C)).app X) :=
  ⟨((functorialFactorizationData (trivialCofibrations C) (fibrations C)).hi
    (Arrow.mk (terminal.from X))).1⟩

instance (X : C) : WeakEquivalence ((fibrantReplacementUnit (C := C)).app X) :=
  ⟨((functorialFactorizationData (trivialCofibrations C) (fibrations C)).hi
    (Arrow.mk (terminal.from X))).2⟩

end FibrantReplacement

end HomotopicalAlgebra

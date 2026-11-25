/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.LocalizationCofibrantRepresentatives

/-!
# The SAME original terminal object after model localization

Every localized object has a genuine cofibrant representative. The
fundamental lemma represents every map into the original fibrant terminal
object, where original uniqueness proves localized uniqueness. The actual
terminal object and its complete projected arrows remain unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v uH vH
open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.ModelLocalization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]

/-- The actual original terminal arrow from a genuine representative gives its complete localized
arrow. -/
def terminalFrom (K : H) : K ⟶ Q.obj (⊤_ C) :=
  (cofibrantRepresentativeIso Q K).inv ≫ Q.map (terminal.from (cofibrantRepresentative Q K).obj)

/-- The SAME original terminal object is genuinely terminal in every given model localization. -/
def terminalIsTerminal : IsTerminal (Q.obj (⊤_ C)) := by
  let _ : IsFibrant (⊤_ C) :=
    (isFibrant_iff_of_isTerminal (𝟙 (⊤_ C)) CategoryTheory.Limits.terminalIsTerminal).mpr
      inferInstance
  apply IsTerminal.ofUniqueHom (terminalFrom Q)
  intro K m
  apply (cancel_epi (cofibrantRepresentativeIso Q K).hom).mp
  calc
    (cofibrantRepresentativeIso Q K).hom ≫ m = Q.map (liftToFibrant Q m) :=
      (liftToFibrant_fac Q m).symm
    _ = Q.map (terminal.from (cofibrantRepresentative Q K).obj) :=
      congrArg Q.map (Subsingleton.elim _ _)
    _ = (cofibrantRepresentativeIso Q K).hom ≫ terminalFrom Q K := by
      rw [terminalFrom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

include Q in
/-- The actual original terminal cone supplies the terminal-limit instance in the given
localization. -/
theorem hasTerminal : HasTerminal H := (terminalIsTerminal Q).hasTerminal

end HomotopicalAlgebra.ModelLocalization

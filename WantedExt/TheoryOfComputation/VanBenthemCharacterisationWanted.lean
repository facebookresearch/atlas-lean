/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Van Benthem's characterization theorem
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.StandardTranslation
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.VanBenthemWanted

open FirstOrder FirstOrder.Language Cslib.Modal

/-- Van Benthem's characterization theorem: a one-variable first-order formula over
the modal language (binary `R`, unary `P_a`) is bisimulation-invariant iff it is
equivalent, at every world of every Kripke model, to the standard translation of a
modal formula. The forward direction (modal formulas are bisimulation-invariant) is
proved in `CSLibExt/Logics/Modal/StandardTranslation.lean`
(`bisimulationInvariant_standardTranslation`); the converse uses compactness and
saturation.
Source: J. van Benthem, "Modal Correspondence Theory", PhD thesis, University of
Amsterdam, 1976, and "Modal Logic and Classical Logic", Bibliopolis, 1983; see also
P. Blackburn, M. de Rijke, Y. Venema, Modal Logic, Cambridge University Press, 2001,
§2.7. -/
public theorem_wanted van_benthem_characterisation {Atom : Type}
    (α : (modalLanguage Atom).BoundedFormula Empty 1)
    (hinv : BisimulationInvariant α) :
    ∃ φ : Cslib.Modal.Formula Atom,
      ∀ {W : Type} (M : Cslib.Modal.KripkeModel W Atom) (w : W),
        @BoundedFormula.Realize (modalLanguage Atom) W (kripkeStructure M) Empty 1 α
          (fun x => x.elim) (fun _ => w) ↔
        @BoundedFormula.Realize (modalLanguage Atom) W (kripkeStructure M) Empty 1
          (standardTranslation 1 (Term.var (Sum.inr (0 : Fin 1))) φ)
          (fun x => x.elim) (fun _ => w)

end Cslib.Logic.VanBenthemWanted

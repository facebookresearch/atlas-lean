/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Beth definability for first-order logic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Symbols
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.FOLBethWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- Beth definability for first-order logic: if a theory `T` implicitly defines an
`n`-ary relation symbol `R` — any two models of `T` on the same carrier that agree on
every other symbol agree on `R` — then `R` is explicitly definable: there is a formula
`θ` with `n` bound variables that does not use the symbol `R` and that `T` proves
equivalent to `R` in every model. Beth definability is the standard corollary of Craig
interpolation, applied to a theory with two copies of the implicitly defined symbol.
Source: E. Beth, "On Padoa's method in the theory of definition", Indagationes
Mathematicae 15 (1953), 330-339; see also H. Enderton, A Mathematical Introduction to
Logic, 2nd ed., Academic Press, 2001, §2.6. -/
public theorem_wanted fol_beth_definability {L : FirstOrder.Language} {n : ℕ}
    (R : L.Relations n) (T : L.Theory)
    (himpl : ∀ (M : Type) [L.Structure M] [M ⊨ T] (N : Type) [L.Structure N] [N ⊨ T]
      (e : M ≃ N),
      (∀ {l : ℕ} (f : L.Functions l) (xs : Fin l → M),
        e (@Structure.funMap L M _ _ f xs) = @Structure.funMap L N _ _ f (fun i => e (xs i))) →
      (∀ {l : ℕ} (S : L.Relations l) (hS : ∀ (h : l = n), S ≠ h.symm ▸ R) (xs : Fin l → M),
        @Structure.RelMap L M _ _ S xs ↔ @Structure.RelMap L N _ _ S (fun i => e (xs i))) →
      ∀ xs : Fin n → M,
          @Structure.RelMap L M _ _ R xs ↔ @Structure.RelMap L N _ _ R (fun i => e (xs i))) :
    ∃ θ : L.BoundedFormula Empty n,
      Sum.inr ⟨n, R⟩ ∉ formulaSymbols θ ∧
        ∀ (M : Type) [L.Structure M] [M ⊨ T] (xs : Fin n → M),
          @Structure.RelMap L M _ _ R xs ↔ θ.Realize (fun x => x.elim) xs

end Cslib.Logic.FOLBethWanted

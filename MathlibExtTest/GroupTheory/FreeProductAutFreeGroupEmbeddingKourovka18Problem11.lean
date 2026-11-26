/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11

open MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11Wanted

namespace MathlibExtTest.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11

private abbrev FullAut : Subgroup (MulAut (FreeGroup (Fin 2))) := ⊤

private def swapGenerators : FullAut :=
  ⟨FreeGroup.freeGroupCongr (Equiv.swap (0 : Fin 2) 1), Subgroup.mem_top _⟩

-- The copies of a nonidentity generator swap in the two factors have distinct images.
example :
    ∃ (m : ℕ) (f : Monoid.Coprod FullAut FullAut →* MulAut (FreeGroup (Fin m))),
      Function.Injective f ∧
        f (Monoid.Coprod.inl swapGenerators) ≠ f (Monoid.Coprod.inr swapGenerators) := by
  obtain ⟨m, f, hf⟩ := freeProductAutFreeGroupEmbeds_holds 2 le_rfl FullAut FullAut
  refine ⟨m, f, hf, ?_⟩
  intro he
  have hSwap : swapGenerators = 1 := by
    simpa using congrArg Monoid.Coprod.fst (hf he)
  have hVal := DFunLike.congr_fun (congrArg Subtype.val hSwap) (FreeGroup.of (0 : Fin 2))
  have hFin : (1 : Fin 2) = 0 := by
    apply FreeGroup.of_injective
    simpa [swapGenerators] using hVal
  exact (by decide : (1 : Fin 2) ≠ 0) hFin

-- The conclusion also applies at the smallest permitted rank with a trivial factor.
example :
    ∃ (m : ℕ) (f : Monoid.Coprod (⊥ : Subgroup (MulAut (FreeGroup (Fin 2)))) FullAut →*
      MulAut (FreeGroup (Fin m))), Function.Injective f :=
  freeProductAutFreeGroupEmbeds_holds 2 le_rfl ⊥ FullAut

end MathlibExtTest.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11

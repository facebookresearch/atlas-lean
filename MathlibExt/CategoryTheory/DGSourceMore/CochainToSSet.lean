/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/DoldKan/Cochain.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.HomologyMonoidalTruncLE
public import MathlibExt.CategoryTheory.DGSourceMore.DoldKanMonoidal
public import MathlibExt.CategoryTheory.DGSourceMore.SimplicialGroupKan
public import MathlibExt.CategoryTheory.DGSourceMore.ModuleForgetMonoidal

/-!
# From cochain complexes to Kan complexes

Good truncation and Dold–Kan send a cochain complex `K` to the underlying simplicial set
of `Γ(K.truncLE' embeddingDownNat)`. In particular degree zero uses cycles, rather than
the whole of `K.X 0`. This functor is lax monoidal, using the lax good truncation and
the Alexander–Whitney lax structure on `Γ`, and its values are Kan complexes by Moore's
theorem for simplicial groups. It supplies the mapping objects for simplicial enrichment
of differential graded categories.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.DGSource

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- Send a cochain complex to the underlying simplicial set of the Dold–Kan image of its
good homological truncation. The values of this functor are Kan complexes.
Its nonnegative chain degree `n` corresponds to cochain degree `-n`. -/
def cochainToSSet : CochainComplex (ModuleCat.{u} R) ℤ ⥤ SSet.{u} :=
  ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R) ⋙
    Idempotents.DoldKan.Γ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R))

/-- The simplicial set assigned to a complex is the underlying simplicial module of
its good truncation under Dold–Kan. -/
theorem cochainToSSet_obj (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainToSSet R).obj K =
      Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat.{u} R) :=
  (rfl)

-- The map, unit, and tensor formulas below rewrite their expected Hom types using
-- cochainToSSet_obj because the functor body is unexposed. Their proofs are definitional.
/-- On morphisms, apply good truncation, Dold–Kan, and then forget the module structure. -/
theorem cochainToSSet_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    (cochainToSSet R).map f = (by
      simp only [cochainToSSet_obj]
      exact Functor.whiskerRight
        (Idempotents.DoldKan.Γ.map
          ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R)).map f))
        (forget (ModuleCat.{u} R))) :=
  (rfl)

/-- The functor to simplicial sets uses the Alexander–Whitney lax monoidal structure
on Dold–Kan and the lax monoidal good truncation. -/
instance cochainToSSetLaxMonoidal : (cochainToSSet R).LaxMonoidal :=
  inferInstanceAs ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R) ⋙
    Idempotents.DoldKan.Γ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R))).LaxMonoidal)

/-- The lax unit combines the forgetful, Alexander–Whitney, and good-truncation units. -/
theorem cochainToSSet_ε :
    Functor.LaxMonoidal.ε (cochainToSSet R) = (by
      simp only [cochainToSSet_obj]
      exact Functor.LaxMonoidal.ε
          ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R))) ≫
        Functor.whiskerRight (Functor.LaxMonoidal.ε Idempotents.DoldKan.Γ)
          (forget (ModuleCat.{u} R)) ≫
        Functor.whiskerRight (Idempotents.DoldKan.Γ.map
          (Functor.LaxMonoidal.ε
            (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R))))
          (forget (ModuleCat.{u} R))) :=
  (rfl)

/-- The tensor comparison combines the forgetful, Alexander–Whitney, and truncation maps. -/
theorem cochainToSSet_μ (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    Functor.LaxMonoidal.μ (cochainToSSet R) K L = (by
      simp only [cochainToSSet_obj]
      exact Functor.LaxMonoidal.μ
          ((Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R)))
          (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat))
          (Idempotents.DoldKan.Γ.obj (L.truncLE' ComplexShape.embeddingDownNat)) ≫
        Functor.whiskerRight (Functor.LaxMonoidal.μ Idempotents.DoldKan.Γ
          (K.truncLE' ComplexShape.embeddingDownNat) (L.truncLE' ComplexShape.embeddingDownNat))
          (forget (ModuleCat.{u} R)) ≫
        Functor.whiskerRight (Idempotents.DoldKan.Γ.map
          (Functor.LaxMonoidal.μ
            (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R)) K L))
          (forget (ModuleCat.{u} R))) :=
  (rfl)

/-- The simplicial set assigned to every cochain complex is a Kan complex. -/
instance (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    SSet.KanComplex ((cochainToSSet R).obj K) := by
  rw [cochainToSSet_obj]
  infer_instance

end

end MathlibExt.DGSource

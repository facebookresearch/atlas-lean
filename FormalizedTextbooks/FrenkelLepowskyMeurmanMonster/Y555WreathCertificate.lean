/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
A source-faithful certificate interface for recognition by concrete wreath
product generators. It separates relation checks, generation, and faithfulness.
No certificate or unconditional recognition theorem is asserted to exist.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555WreathGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.BimonsterRecognitionTransport

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

variable {M : Type*} [Group M]

/-- Exactly the finite factor checks needed for the primary-source relators.
All involution checks are already proved by the concrete parameterization. -/
structure Y555WreathRelationCertificate (m : Y555Vertex → M) : Prop where
  center : m none = 1
  coxeter : ∀ u v, u ≠ v →
    (m u * (m v)⁻¹) ^ (if y555Adjacent u v then 3 else 2 : ℕ) = 1
  spider : (y555SpiderFirst m * y555SpiderSecond m) ^ 5 = 1

/-- The finite factor certificate verifies every defining relator. -/
theorem y555Wreath_relations (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m) (r : FreeGroup Y555Vertex)
    (hr : r ∈ y555Relations) :
    FreeGroup.lift (fun v => y555WreathReflection (m v)) r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, huv, rfl⟩ | rfl
  · simp only [map_pow, FreeGroup.lift_apply_of, y555WreathReflection_sq]
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
    exact (y555WreathReflection_mul_pow _ _ _).mpr (h.coxeter u v huv)
  · rw [map_pow]
    exact (y555WreathSpider_tenth m h.center).mpr h.spider

/-- The actual homomorphism obtained after checking the concrete factor words. -/
def y555WreathMap (m : Y555Vertex → M) (h : Y555WreathRelationCertificate m) :
    BimonsterPresentation →* M ≀ᵣ WreathParity :=
  PresentedGroup.toGroup (y555Wreath_relations m h)

@[simp] theorem y555WreathMap_generator (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m) (v : Y555Vertex) :
    y555WreathMap m h (PresentedGroup.of v) = y555WreathReflection (m v) :=
  PresentedGroup.toGroup.of (y555Wreath_relations m h)

@[simp] theorem y555WreathMap_swap (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m) :
    y555WreathMap m h bimonsterSwap = wreathSwap M := by
  change y555WreathMap m h (PresentedGroup.of none) = _
  rw [y555WreathMap_generator, h.center, y555WreathReflection_one]

/-- Generation is an independent obligation on the concrete generator family.
Relation checks alone do not establish it. -/
theorem y555WreathMap_surjective_iff (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m) :
    Function.Surjective (y555WreathMap m h) ↔
      Subgroup.closure (Set.range (fun v => y555WreathReflection (m v))) = ⊤ := by
  rw [← FreeGroup.lift_surjective_iff_closure_range_eq_top]
  constructor
  · intro hs g
    obtain ⟨p, hp⟩ := hs g
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective y555Relations p
    refine ⟨w, ?_⟩
    have hh := (congrArg (y555WreathMap m h) hw).trans hp
    change y555WreathMap m h (QuotientGroup.mk w) = g at hh
    exact hh
  · intro hs
    exact QuotientGroup.lift_surjective_of_surjective _ _ hs
      (PresentedGroup.closure_rels_subset_ker (y555Wreath_relations m h))

/-- Faithfulness is precisely the full kernel certificate: every factor word
killed by the concrete evaluation must follow from the published relators. -/
theorem y555WreathMap_injective_iff (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m) :
    Function.Injective (y555WreathMap m h) ↔
      Subgroup.normalClosure y555Relations =
        (FreeGroup.lift (fun v => y555WreathReflection (m v))).ker := by
  exact QuotientGroup.injective_lift_iff _ _
    (PresentedGroup.closure_rels_subset_ker (y555Wreath_relations m h))

/-- Assemble a genuine recognition only after independent relation, generation,
and full-kernel certificates have all been provided. -/
noncomputable def y555WreathRecognition (m : Y555Vertex → M) (h : Y555WreathRelationCertificate m)
    (hgen : Subgroup.closure (Set.range (fun v => y555WreathReflection (m v))) = ⊤)
    (hker : Subgroup.normalClosure y555Relations =
      (FreeGroup.lift (fun v => y555WreathReflection (m v))).ker) :
    BimonsterPresentation ≃* M ≀ᵣ WreathParity :=
  MulEquiv.ofBijective (y555WreathMap m h)
    ⟨(y555WreathMap_injective_iff m h).mpr hker,
      (y555WreathMap_surjective_iff m h).mpr hgen⟩

/-- Recognition certificates for the actual factor identify the independent
classical centralizer quotient. No named copy or recognition axiom is used. -/
noncomputable def classicalMonsterOfWreathCertificate (m : Y555Vertex → M)
    (h : Y555WreathRelationCertificate m)
    (hgen : Subgroup.closure (Set.range (fun v => y555WreathReflection (m v))) = ⊤)
    (hker : Subgroup.normalClosure y555Relations =
      (FreeGroup.lift (fun v => y555WreathReflection (m v))).ker) :
    classicalMonster ≃* M :=
  classicalMonsterComparison (y555WreathRecognition m h hgen hker)
    (y555WreathMap_swap m h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

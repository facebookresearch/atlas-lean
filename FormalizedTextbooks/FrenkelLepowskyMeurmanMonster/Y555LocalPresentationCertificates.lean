/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Kernel-checkable products of conjugates of the exact C322 defining relators.
This is a certificate format, not a coset-enumeration or recognition assumption. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source local relators: eight squares, Coxeter pairs, and the tenth spider power. -/
abbrev Y322RelatorIndex := Fin 8 ⊕ (Fin 8 × Fin 8) ⊕ Unit

/-- A finite indexed family of literal relators in the independently presented local group. -/
def y322IndexedRelator : Y322RelatorIndex → FreeGroup (Fin 8)
  | .inl v => FreeGroup.of v ^ 2
  | .inr (.inl (u, v)) =>
      (FreeGroup.of u * FreeGroup.of v) ^
        (if y555Adjacent (y322Vertex u) (y322Vertex v) then 3 else 2 : ℕ)
  | .inr (.inr _) => y322Spider ^ 10

/-- Each indexed relator vanishes in the actual local presentation.
Repeated-vertex Coxeter pairs vanish by the corresponding generator square. -/
theorem y322IndexedRelator_valid (i : Y322RelatorIndex) :
    PresentedGroup.mk y322Relations
      (y322IndexedRelator i) = 1 := by
  rcases i with v | ⟨u, v⟩ | ⟨⟩
  · simpa only [y322IndexedRelator, map_pow, PresentedGroup.of] using
      PresentedGroup.one_of_mem (rels := y322Relations)
        (show FreeGroup.of v ^ 2 ∈ y322Relations from Or.inl ⟨v, rfl⟩)
  · by_cases h : u = v
    · subst v
      have hs := PresentedGroup.one_of_mem (rels := y322Relations)
        (show FreeGroup.of u ^ 2 ∈ y322Relations from Or.inl ⟨u, rfl⟩)
      have hm : PresentedGroup.mk y322Relations (FreeGroup.of u) *
          PresentedGroup.mk y322Relations (FreeGroup.of u) = 1 := by
        simpa only [map_pow, pow_two, map_mul] using hs
      simp [y322IndexedRelator, hm, y555Adjacent_irrefl]
    · simpa only [y322IndexedRelator, map_pow, map_mul, PresentedGroup.of] using
        PresentedGroup.one_of_mem (rels := y322Relations)
          (show y322IndexedRelator (.inr (.inl (u, v))) ∈ y322Relations from
            Or.inr (Or.inl ⟨u, v, h, rfl⟩))
  · simpa only [y322IndexedRelator] using
      PresentedGroup.one_of_mem (rels := y322Relations)
        (show y322Spider ^ 10 ∈ y322Relations from Or.inr (Or.inr rfl))

/-- A free word certified as a product of conjugates of genuine defining relators. -/
inductive Y322RelatorCertificate
  | identity
  | relator (i : Y322RelatorIndex)
  | multiply (left right : Y322RelatorCertificate)
  | inverse (certificate : Y322RelatorCertificate)
  | conjugate (word : FreeGroup (Fin 8)) (certificate : Y322RelatorCertificate)

/-- The exact free word encoded by a relator certificate; free cancellation is automatic. -/
def y322CertificateWord : Y322RelatorCertificate → FreeGroup (Fin 8)
  | .identity => 1
  | .relator i => y322IndexedRelator i
  | .multiply left right => y322CertificateWord left * y322CertificateWord right
  | .inverse c => (y322CertificateWord c)⁻¹
  | .conjugate w c => w * y322CertificateWord c * w⁻¹

/-- Every certificate proves its exact free word is trivial in the source local quotient. -/
theorem y322CertificateWord_valid (c : Y322RelatorCertificate) :
    PresentedGroup.mk y322Relations
      (y322CertificateWord c) = 1 := by
  induction c with
  | identity => simp [y322CertificateWord]
  | relator i => exact y322IndexedRelator_valid i
  | multiply left right hl hr => simp [y322CertificateWord, hl, hr]
  | inverse c hc => simp [y322CertificateWord, hc]
  | conjugate w c hc => simp [y322CertificateWord, hc]

/-- Comparing a certificate with a target free word supplies an actual local identity. -/
theorem y322Certificate_proves (c : Y322RelatorCertificate) (w : FreeGroup (Fin 8))
    (hw : y322CertificateWord c = w) :
    PresentedGroup.mk y322Relations w = 1 := by
  rw [← hw]
  exact y322CertificateWord_valid c

/-- The same checked word identity holds at the genuine restricted Y555 vertices. -/
theorem y322Certificate_proves_Y555 (c : Y322RelatorCertificate)
    (w : FreeGroup (Fin 8)) (hw : y322CertificateWord c = w) :
    FreeGroup.lift (fun v => (PresentedGroup.of (y322Vertex v) : BimonsterPresentation))
      w = 1 := by
  have he : y322IntoY555.comp (PresentedGroup.mk y322Relations) =
      FreeGroup.lift (fun v =>
        (PresentedGroup.of (y322Vertex v) : BimonsterPresentation)) := by
    apply FreeGroup.ext_hom
    intro v
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact y322IntoY555_generator v
  rw [← he, MonoidHom.comp_apply, y322Certificate_proves c w hw, map_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

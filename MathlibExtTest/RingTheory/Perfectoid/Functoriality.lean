/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Perfectoid.Functoriality

@[expose] public noncomputable section

open Localization

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
  [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]
  [IsAdicComplete (Ideal.span {(p : R)}) R] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- The coefficients of the image of `x` under the tilt map are the images of its coefficients
modulo `p`. -/
example (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    PreTilt.coeff n (PreTilt.map p f x) = ModP.map p f (PreTilt.coeff n x) := by
  simp

/-- The tilt map of the identity fixes every element. -/
example (x : PreTilt R p) : PreTilt.map p (RingHom.id R) x = x := by
  simp

/-- The tilt map of a composite is the composite of the tilt maps. -/
example (g : S →+* R) (f : R →+* S) (x : PreTilt R p) :
    PreTilt.map p (g.comp f) x = PreTilt.map p g (PreTilt.map p f x) := by
  rw [PreTilt.map_comp, RingHom.comp_apply]

/-- The untilt of the image of `x` under the tilt map is the image of the untilt of `x`. -/
example (f : R →+* S) (x : PreTilt R p) : (PreTilt.map p f x).untilt = f x.untilt := by
  simp

/-- `θ_S` of the image of a Teichmüller representative `[x]` is the image of the untilt of
`x`. -/
example (f : R →+* S) (x : PreTilt R p) :
    WittVector.fontaineTheta S p
        (WittVector.map (PreTilt.map p f) (WittVector.teichmuller p x)) = f x.untilt := by
  simp

/-- Naturality of `θ[1/p]`, pointwise. -/
example (f : R →+* S) (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    fontaineThetaInvertP S p (awayMapNatCast (WittVector.map (PreTilt.map p f)) p x) =
      awayMapNatCast f p (fontaineThetaInvertP R p x) := by
  rw [← RingHom.comp_apply, fontaineThetaInvertP_comp_awayMapNatCast, RingHom.comp_apply]

/-- The map on `R[1/n]` of the identity fixes every element. -/
example (n : ℕ) (x : Localization.Away (n : R)) : awayMapNatCast (RingHom.id R) n x = x := by
  simp

/-- The adic completion map extends the ring map. -/
example {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B) (f : A →+* B)
    (h : I.map f ≤ J) (x : A) :
    AdicCompletion.mapRingHom I J f h (AdicCompletion.of I A x) = AdicCompletion.of J B (f x) := by
  simp

/-- The map of adic completions induced by the identity fixes every element. -/
example {A : Type*} [CommRing A] (I : Ideal A) (h : I.map (RingHom.id A) ≤ I)
    (x : AdicCompletion I A) : AdicCompletion.mapRingHom I I (RingHom.id A) h x = x := by
  simp

/-- The map of adic completions induced by a composite is the composite of the maps. -/
example {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] (I : Ideal A) (J : Ideal B)
    (K : Ideal C) (g : B →+* C) (f : A →+* B) (hg : J.map g ≤ K) (hf : I.map f ≤ J)
    (hgf : I.map (g.comp f) ≤ K) (x : AdicCompletion I A) :
    AdicCompletion.mapRingHom I K (g.comp f) hgf x =
      AdicCompletion.mapRingHom J K g hg (AdicCompletion.mapRingHom I J f hf x) := by
  rw [AdicCompletion.mapRingHom_comp I J K g f hg hf, RingHom.comp_apply]

/-- An action of an endomorphism `f` on `W(R♭)[1/p]` written with `Localization.awayLift` from
the coordinatewise action `Perfection.map p (Ideal.quotientMap _ f h)` on the tilt is, by
definition, `awayMapNatCast (WittVector.map (PreTilt.map p f)) p`. -/
example (f : R →+* R) (h : Ideal.span {(p : R)} ≤ (Ideal.span {(p : R)}).comap f)
    (hu : IsUnit (((algebraMap (WittVector p (PreTilt R p))
      (Localization.Away (p : WittVector p (PreTilt R p)))).comp
        (WittVector.map (Perfection.map p (Ideal.quotientMap (Ideal.span {(p : R)}) f h) :
          PreTilt R p →+* PreTilt R p))) (p : WittVector p (PreTilt R p)))) :
    Localization.awayLift ((algebraMap (WittVector p (PreTilt R p))
        (Localization.Away (p : WittVector p (PreTilt R p)))).comp
          (WittVector.map (Perfection.map p (Ideal.quotientMap (Ideal.span {(p : R)}) f h) :
            PreTilt R p →+* PreTilt R p))) (p : WittVector p (PreTilt R p)) hu =
      awayMapNatCast (WittVector.map (PreTilt.map p f)) p :=
  rfl

/-- So such an action maps the kernel of `θ[1/p]` into itself: this is
`ker_fontaineThetaInvertP_le_comap` for `f`. -/
example (f : R →+* R) (h : Ideal.span {(p : R)} ≤ (Ideal.span {(p : R)}).comap f)
    (hu : IsUnit (((algebraMap (WittVector p (PreTilt R p))
      (Localization.Away (p : WittVector p (PreTilt R p)))).comp
        (WittVector.map (Perfection.map p (Ideal.quotientMap (Ideal.span {(p : R)}) f h) :
          PreTilt R p →+* PreTilt R p))) (p : WittVector p (PreTilt R p)))) :
    RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP R p)).comap
        (Localization.awayLift ((algebraMap (WittVector p (PreTilt R p))
          (Localization.Away (p : WittVector p (PreTilt R p)))).comp
            (WittVector.map (Perfection.map p (Ideal.quotientMap (Ideal.span {(p : R)}) f h) :
              PreTilt R p →+* PreTilt R p))) (p : WittVector p (PreTilt R p)) hu) :=
  ker_fontaineThetaInvertP_le_comap p f

/-- The continuous extension to `B_dR^+` of an action of `f` on `W(R♭)[1/p]` preserving
`ker θ`, written with `AdicCompletion.liftRingHom` and `Ideal.quotientMap`, is by definition
`BDeRhamPlus.map p f`. -/
example (f : R →+* R)
    (h : ∀ n, RingHom.ker (fontaineThetaInvertP R p) ^ n ≤
      (RingHom.ker (fontaineThetaInvertP R p) ^ n).comap
        (awayMapNatCast (WittVector.map (PreTilt.map p f)) p))
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (RingHom.ker (fontaineThetaInvertP R p)) hle).comp
        ((Ideal.quotientMap _ (awayMapNatCast (WittVector.map (PreTilt.map p f)) p) (h n)).comp
          (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) n).toRingHom) =
      (Ideal.quotientMap _ (awayMapNatCast (WittVector.map (PreTilt.map p f)) p) (h m)).comp
        (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) m).toRingHom) :
    (AdicCompletion.liftRingHom (RingHom.ker (fontaineThetaInvertP R p))
      (fun n => (Ideal.quotientMap _ (awayMapNatCast (WittVector.map (PreTilt.map p f)) p)
        (h n)).comp (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP R p)) n).toRingHom)
      hf : BDeRhamPlus R p →+* BDeRhamPlus R p) = BDeRhamPlus.map p f :=
  rfl

/-- The algebra map `W(R♭)[1/p] → B_dR^+(R)` is `AdicCompletion.of`. -/
example (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    algebraMap _ (BDeRhamPlus R p) x =
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ x : BDeRhamPlus R p) :=
  rfl

/-- `BDeRhamPlus.map` extends the map on `W(R♭)[1/p]`. -/
example (f : R →+* S) (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    BDeRhamPlus.map p f (algebraMap _ (BDeRhamPlus R p) x) =
      algebraMap _ (BDeRhamPlus S p) (awayMapNatCast (WittVector.map (PreTilt.map p f)) p x) := by
  simp

/-- The map on `B_dR^+` of the identity fixes every element. -/
example (x : BDeRhamPlus R p) : BDeRhamPlus.map p (RingHom.id R) x = x := by
  simp

/-- The map on `B_dR^+` of a composite is the composite of the maps. -/
example (g : S →+* R) (f : R →+* S) (x : BDeRhamPlus R p) :
    BDeRhamPlus.map p (g.comp f) x = BDeRhamPlus.map p g (BDeRhamPlus.map p f x) := by
  rw [BDeRhamPlus.map_comp, RingHom.comp_apply]

/-- The maps on `B_dR^+` of a ring isomorphism and of its inverse are inverse to each other. -/
example (e : R ≃+* S) (x : BDeRhamPlus R p) :
    BDeRhamPlus.map p e.symm.toRingHom (BDeRhamPlus.map p e.toRingHom x) = x := by
  rw [← RingHom.comp_apply, ← BDeRhamPlus.map_comp, RingEquiv.symm_toRingHom_comp_toRingHom,
    BDeRhamPlus.map_id, RingHom.id_apply]

/-- A ring isomorphism maps generators of `ker θ[1/p]` to generators. -/
example (e : R ≃+* S) (a : Localization.Away (p : WittVector p (PreTilt R p)))
    (ha : RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}) :
    RingHom.ker (fontaineThetaInvertP S p) =
      Ideal.span {awayMapNatCast (WittVector.map (PreTilt.map p e.toRingHom)) p a} :=
  ker_fontaineThetaInvertP_eq_span_awayMapNatCast p e a ha

/-- The map on `B_dR` of a ring isomorphism extends the map on `W(R♭)[1/p]`. -/
example (e : R ≃+* S) (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    BDeRham.mapOfRingEquiv p e
        (algebraMap (BDeRhamPlus R p) (BDeRham R p) (algebraMap _ (BDeRhamPlus R p) x)) =
      algebraMap (BDeRhamPlus S p) (BDeRham S p)
        (algebraMap _ (BDeRhamPlus S p)
          (awayMapNatCast (WittVector.map (PreTilt.map p e.toRingHom)) p x)) := by
  simp

/-- The image in `B_dR` of a generator of `ker θ` is a unit. -/
example (a : Localization.Away (p : WittVector p (PreTilt R p)))
    (ha : RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}) :
    IsUnit (algebraMap (BDeRhamPlus R p) (BDeRham R p) (algebraMap _ (BDeRhamPlus R p) a)) :=
  IsLocalization.map_units (BDeRham R p)
    (⟨_, BDeRham.algebraMap_mem_submonoid p ha⟩ : BDeRham.submonoid R p)

/-- The map on `B_dR` of the identity isomorphism fixes every element. -/
example (x : BDeRham R p) : BDeRham.mapOfRingEquiv p (RingEquiv.refl R) x = x := by
  simp

/-- The map on `B_dR` of a composite of ring isomorphisms is the composite of their maps. -/
example (e₁ : R ≃+* S) (e₂ : S ≃+* R) (x : BDeRham R p) :
    BDeRham.mapOfRingEquiv p (e₁.trans e₂) x =
      BDeRham.mapOfRingEquiv p e₂ (BDeRham.mapOfRingEquiv p e₁ x) := by
  rw [BDeRham.mapOfRingEquiv_trans, RingHom.comp_apply]

/-- The maps on `B_dR` of a ring isomorphism and of its inverse are inverse to each other. -/
example (e : R ≃+* S) (x : BDeRham R p) :
    BDeRham.mapOfRingEquiv p e.symm (BDeRham.mapOfRingEquiv p e x) = x := by
  rw [← RingHom.comp_apply, ← BDeRham.mapOfRingEquiv_trans, RingEquiv.self_trans_symm,
    BDeRham.mapOfRingEquiv_refl, RingHom.id_apply]

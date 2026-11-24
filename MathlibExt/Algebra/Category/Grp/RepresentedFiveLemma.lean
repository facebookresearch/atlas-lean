/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/
module

public import MathlibExt.Algebra.Category.Grp.ExactnessTransport

/-!
# Five Lemma for represented groups with arbitrary connecting functions

Group operations are needed on the three middle terms of each row.
The outside connecting functions remain arbitrary. Full source
equivalences transport the six exactness laws and four naturality squares,
giving both injectivity and surjectivity of the original middle function.
-/

@[expose] public section

set_option autoImplicit false
namespace GrpCat.NullExactFiveLemma

/-- A five-term chase needs group operations on its three middle terms.
The outside connecting functions retain their actual parametrized images. -/
theorem bijective_of_null_exactness
    {A A' B B' C C' D D' E E' : Type*}
    [Group B] [Group B'] [Group C] [Group C'] [Group D] [Group D']
    (l : A → B) (m : B →* C) (n : C →* D) (r : D → E)
    (l' : A' → B') (m' : B' →* C') (n' : C' →* D') (r' : D' → E')
    (a : A → A') (b : B →* B') (c : C →* C') (d : D →* D') (e : E → E')
    (z : E) (z' : E')
    (hl : Function.MulExact l m)
    (hm : Function.MulExact m n)
    (hn : ∀ x, (∃ y, n y = x) ↔ r x = z)
    (hl' : Function.MulExact l' m')
    (hm' : Function.MulExact m' n')
    (hn' : ∀ x, (∃ y, n' y = x) ↔ r' x = z')
    (hab : ∀ x, b (l x) = l' (a x))
    (hbc : ∀ x, c (m x) = m' (b x))
    (hcd : ∀ x, d (n x) = n' (c x))
    (hde : ∀ x, e (r x) = r' (d x))
    (hz : e z = z')
    (ha : Function.Surjective a) (hb : Function.Bijective b)
    (hd : Function.Bijective d) (he : Function.Injective e) :
    Function.Bijective c := by
  constructor
  · intro x y hxy
    have hc : c (x * y⁻¹) = 1 := by
      rw [c.map_mul, c.map_inv, hxy]
      simp only [mul_inv_cancel]
    have hnd : n (x * y⁻¹) = 1 := by
      apply hd.1
      rw [hcd, hc, n'.map_one, d.map_one]
    obtain ⟨t, ht⟩ := (hm (x * y⁻¹)).mp hnd
    have hmt : m' (b t) = 1 := by
      rw [← hbc, ht, hc]
    obtain ⟨u, hu⟩ := (hl' (b t)).mp hmt
    obtain ⟨v, hv⟩ := ha u
    have hlt : l v = t := by
      apply hb.1
      rw [hab, hv, hu]
    have hzero : m t = 1 := (hl t).mpr ⟨v, hlt⟩
    exact mul_inv_eq_one.mp (ht.symm.trans hzero)
  · intro x'
    have hr' : r' (n' x') = z' := (hn' (n' x')).mp ⟨x', rfl⟩
    obtain ⟨t, ht⟩ := hd.2 (n' x')
    have hrt : r t = z := by
      apply he
      rw [hde, ht, hr', hz]
    obtain ⟨x, hx⟩ := (hn t).mpr hrt
    have hnx : n' (c x) = n' x' := by
      rw [← hcd, hx, ht]
    let residual := x' * (c x)⁻¹
    have hresidual : n' residual = 1 := by
      dsimp only [residual]
      rw [n'.map_mul, n'.map_inv, hnx]
      simp only [mul_inv_cancel]
    obtain ⟨t', ht'⟩ := (hm' residual).mp hresidual
    obtain ⟨t, hbt⟩ := hb.2 t'
    refine ⟨m t * x, ?_⟩
    rw [c.map_mul, hbc, hbt, ht']
    dsimp only [residual]
    simp only [mul_assoc, inv_mul_cancel, mul_one]


end GrpCat.NullExactFiveLemma

namespace GrpCat.NullExactSequenceTransfer

/-- Full null-kernel exactness transports through the three complete original Hom equivalences. -/
theorem exact_transfer
    {A B C GA GB GC : Type*}
    (a : A ≃ GA) (b : B ≃ GB) (c : C ≃ GC)
    (f : A → B) (g : B → C) (fG : GA → GB) (gG : GB → GC)
    (z : C) (zG : GC) (hz : c z = zG)
    (hf : ∀ x, b (f x) = fG (a x)) (hg : ∀ x, c (g x) = gG (b x))
    (he : ∀ x, (∃ y, f y = x) ↔ g x = z) :
    ∀ x, (∃ y, fG y = x) ↔ gG x = zG := by
  intro x
  constructor
  · rintro ⟨y, hy⟩
    have hfy : f (a.symm y) = b.symm x := by
      apply b.injective
      rw [hf, a.apply_symm_apply, hy, b.apply_symm_apply]
    have h := congrArg c ((he (b.symm x)).mp ⟨a.symm y, hfy⟩)
    rw [hg, b.apply_symm_apply, hz] at h
    exact h
  · intro hx
    have hgx : g (b.symm x) = z := by
      apply c.injective
      rw [hg, b.apply_symm_apply, hz]
      exact hx
    obtain ⟨y, hy⟩ := (he (b.symm x)).mpr hgx
    refine ⟨a y, ?_⟩
    rw [← hf, hy, b.apply_symm_apply]

/-- The entire original vertical function is bijective exactly when its represented group
function is. -/
theorem bijective_transfer
    {A B GA GB : Type*} (a : A ≃ GA) (b : B ≃ GB)
    (f : A → B) (fG : GA → GB) (hf : ∀ x, b (f x) = fG (a x)) :
    Function.Bijective f ↔ Function.Bijective fG := by
  constructor
  · intro h
    let e := a.symm.trans ((Equiv.ofBijective f h).trans b)
    have he : (e : GA → GB) = fG := by
      funext x
      exact (hf (a.symm x)).trans (congrArg fG (a.apply_symm_apply x))
    have hb := e.bijective
    rw [he] at hb
    exact hb
  · intro h
    let e := a.trans ((Equiv.ofBijective fG h).trans b.symm)
    have he : (e : A → B) = f := by
      funext x
      apply b.injective
      exact (b.apply_symm_apply (fG (a x))).trans (hf x).symm
    have hb := e.bijective
    rw [he] at hb
    exact hb


end GrpCat.NullExactSequenceTransfer

namespace GrpCat.RepresentedFiveLemma

open GrpCat.NullExactSequenceTransfer GrpCat.NullExactFiveLemma

/-- The original five-term Hom ladder transfers to its actual three middle represented groups,
retaining the entire original connecting functions, six exactness laws and four source squares. -/
theorem fiveLemma
    {A B C D E A' B' C' D' E' GB GC GD GB' GC' GD' : Type*}
    [Group GB] [Group GC] [Group GD] [Group GB'] [Group GC'] [Group GD']
    (eb : B ≃ GB) (ec : C ≃ GC) (ed : D ≃ GD)
    (eb' : B' ≃ GB') (ec' : C' ≃ GC') (ed' : D' ≃ GD')
    (l : A → B) (m : B → C) (n : C → D) (r : D → E)
    (l' : A' → B') (m' : B' → C') (n' : C' → D') (r' : D' → E')
    (a : A → A') (b : B → B') (c : C → C') (d : D → D') (e : E → E')
    (mg : GB →* GC) (ng : GC →* GD) (mg' : GB' →* GC') (ng' : GC' →* GD')
    (bg : GB →* GB') (cg : GC →* GC') (dg : GD →* GD')
    (zc : C) (zd : D) (ze : E) (zc' : C') (zd' : D') (ze' : E')
    (hzc : ec zc = 1) (hzd : ed zd = 1) (hzc' : ec' zc' = 1) (hzd' : ed' zd' = 1)
    (hm : ∀ x, ec (m x) = mg (eb x)) (hn : ∀ x, ed (n x) = ng (ec x))
    (hm' : ∀ x, ec' (m' x) = mg' (eb' x)) (hn' : ∀ x, ed' (n' x) = ng' (ec' x))
    (hb : ∀ x, eb' (b x) = bg (eb x)) (hc : ∀ x, ec' (c x) = cg (ec x))
    (hd : ∀ x, ed' (d x) = dg (ed x))
    (hlExact : ∀ x, (∃ y, l y = x) ↔ m x = zc)
    (hmExact : ∀ x, (∃ y, m y = x) ↔ n x = zd)
    (hnExact : ∀ x, (∃ y, n y = x) ↔ r x = ze)
    (hlExact' : ∀ x, (∃ y, l' y = x) ↔ m' x = zc')
    (hmExact' : ∀ x, (∃ y, m' y = x) ↔ n' x = zd')
    (hnExact' : ∀ x, (∃ y, n' y = x) ↔ r' x = ze')
    (hab : ∀ x, b (l x) = l' (a x)) (hbc : ∀ x, c (m x) = m' (b x))
    (hcd : ∀ x, d (n x) = n' (c x)) (hde : ∀ x, e (r x) = r' (d x))
    (hze : e ze = ze')
    (haBij : Function.Surjective a) (hbBij : Function.Bijective b)
    (hdBij : Function.Bijective d) (heBij : Function.Injective e) :
    Function.Bijective c := by
  have hbGroup : Function.Bijective bg := (bijective_transfer eb eb' b bg hb).mp hbBij
  have hdGroup : Function.Bijective dg := (bijective_transfer ed ed' d dg hd).mp hdBij
  have hGroup : Function.Bijective cg :=
    bijective_of_null_exactness
      (fun x => eb (l x)) mg ng (fun x => r (ed.symm x))
      (fun x => eb' (l' x)) mg' ng' (fun x => r' (ed'.symm x))
      a bg cg dg e ze ze'
      (fun x => (exact_transfer (Equiv.refl A) eb ec l m (fun x => eb (l x)) mg zc 1 hzc
        (fun _ => rfl) hm hlExact x).symm)
      (fun x => (exact_transfer eb ec ed m n mg ng zd 1 hzd hm hn hmExact x).symm)
      (exact_transfer ec ed (Equiv.refl E) n r ng (fun x => r (ed.symm x)) ze ze rfl hn
        (fun x => congrArg r (ed.symm_apply_apply x).symm) hnExact)
      (fun x => (exact_transfer (Equiv.refl A') eb' ec' l' m' (fun x => eb' (l' x)) mg' zc' 1 hzc'
        (fun _ => rfl) hm' hlExact' x).symm)
      (fun x => (exact_transfer eb' ec' ed' m' n' mg' ng' zd' 1 hzd' hm' hn' hmExact' x).symm)
      (exact_transfer ec' ed' (Equiv.refl E') n' r' ng' (fun x => r' (ed'.symm x)) ze' ze' rfl hn'
        (fun x => congrArg r' (ed'.symm_apply_apply x).symm) hnExact')
      (fun x => (hb (l x)).symm.trans (congrArg eb' (hab x)))
      (by
        intro x
        obtain ⟨y, rfl⟩ := eb.surjective x
        exact (congrArg cg (hm y).symm).trans
          ((hc (m y)).symm.trans ((congrArg ec' (hbc y)).trans ((hm' (b y)).trans
            (congrArg mg' (hb y))))))
      (by
        intro x
        obtain ⟨y, rfl⟩ := ec.surjective x
        exact (congrArg dg (hn y).symm).trans
          ((hd (n y)).symm.trans ((congrArg ed' (hcd y)).trans ((hn' (c y)).trans
            (congrArg ng' (hc y))))))
      (by
        intro x
        obtain ⟨y, rfl⟩ := ed.surjective x
        rw [ed.symm_apply_apply]
        have h : ed'.symm (dg (ed y)) = d y := by
          apply ed'.injective
          exact (ed'.apply_symm_apply _).trans (hd y).symm
        rw [h]
        exact hde y)
      hze haBij hbGroup hdGroup heBij
  exact (bijective_transfer ec ec' c cg hc).mpr hGroup


end GrpCat.RepresentedFiveLemma

universe wB wC wD wB' wC' wD'

namespace GrpCat.RepresentedFiveLemma


/-- The same full chase is typed on actual bundled groups before they are instantiated. -/
theorem bundledFiveLemma
    {A B C D E A' B' C' D' E' : Type*}
    (GB : GrpCat.{wB}) (GC : GrpCat.{wC}) (GD : GrpCat.{wD})
    (GB' : GrpCat.{wB'}) (GC' : GrpCat.{wC'}) (GD' : GrpCat.{wD'})
    (eb : B ≃ GB) (ec : C ≃ GC) (ed : D ≃ GD)
    (eb' : B' ≃ GB') (ec' : C' ≃ GC') (ed' : D' ≃ GD')
    (l : A → B) (m : B → C) (n : C → D) (r : D → E)
    (l' : A' → B') (m' : B' → C') (n' : C' → D') (r' : D' → E')
    (a : A → A') (b : B → B') (c : C → C') (d : D → D') (e : E → E')
    (mg : GB →* GC) (ng : GC →* GD) (mg' : GB' →* GC') (ng' : GC' →* GD')
    (bg : GB →* GB') (cg : GC →* GC') (dg : GD →* GD')
    (zc : C) (zd : D) (ze : E) (zc' : C') (zd' : D') (ze' : E')
    (hzc : ec zc = 1) (hzd : ed zd = 1)
    (hzc' : ec' zc' = 1) (hzd' : ed' zd' = 1)
    (hm : ∀ x, ec (m x) = mg (eb x)) (hn : ∀ x, ed (n x) = ng (ec x))
    (hm' : ∀ x, ec' (m' x) = mg' (eb' x)) (hn' : ∀ x, ed' (n' x) = ng' (ec' x))
    (hb : ∀ x, eb' (b x) = bg (eb x)) (hc : ∀ x, ec' (c x) = cg (ec x))
    (hd : ∀ x, ed' (d x) = dg (ed x))
    (hlExact : ∀ x, (∃ y, l y = x) ↔ m x = zc)
    (hmExact : ∀ x, (∃ y, m y = x) ↔ n x = zd)
    (hnExact : ∀ x, (∃ y, n y = x) ↔ r x = ze)
    (hlExact' : ∀ x, (∃ y, l' y = x) ↔ m' x = zc')
    (hmExact' : ∀ x, (∃ y, m' y = x) ↔ n' x = zd')
    (hnExact' : ∀ x, (∃ y, n' y = x) ↔ r' x = ze')
    (hab : ∀ x, b (l x) = l' (a x)) (hbc : ∀ x, c (m x) = m' (b x))
    (hcd : ∀ x, d (n x) = n' (c x)) (hde : ∀ x, e (r x) = r' (d x))
    (hze : e ze = ze')
    (haBij : Function.Surjective a) (hbBij : Function.Bijective b)
    (hdBij : Function.Bijective d) (heBij : Function.Injective e) :
    Function.Bijective c :=
  fiveLemma eb ec ed eb' ec' ed' l m n r l' m' n' r' a b c d e
    mg ng mg' ng' bg cg dg zc zd ze zc' zd' ze'
    hzc hzd hzc' hzd' hm hn hm' hn' hb hc hd
    hlExact hmExact hnExact hlExact' hmExact' hnExact'
    hab hbc hcd hde hze haBij hbBij hdBij heBij


end GrpCat.RepresentedFiveLemma

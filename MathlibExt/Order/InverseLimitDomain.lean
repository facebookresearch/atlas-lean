/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.ScottContinuity
public import Mathlib.Order.Hom.Basic
public import MathlibExt.Order.ScottContinuity.ContinuousLattice
import MathlibExt.Order.ScottContinuity.FunctionSpace

/-!
# Scott's inverse-limit model `D∞ ≅ [D∞ → D∞]`

Scott solved the domain equation `D ≅ [D → D]` non-trivially by an inverse limit
(D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), §4; published in *Toposes, Algebraic
Geometry and Logic*, Lecture Notes in Math. 274 (1972), 97–136). Starting from a continuous lattice
`D₀` and a projection pair between `D₀` and `D₁ = [D₀ → D₀]`, he sets `Dₙ₊₁ = [Dₙ → Dₙ]` and lifts
the projection pairs; the inverse limit `D∞` is a continuous lattice (Proposition 4.1)
homeomorphic, and in particular order-isomorphic, to its own space of continuous maps
(Theorem 4.4), and each `Dₙ` is a projection of `D∞` (Proposition 4.2). With application `x(y)`
and abstraction transported along this isomorphism, `D∞` is a model of the untyped λ-calculus in
which β and η both hold.

The entry below records Propositions 4.1–4.2 (for `n = 0`) and Theorem 4.4 as one existence
statement, with Scott's hypothesis and Scott's definition of continuous lattices.
-/

@[expose] public section

namespace MathlibExt.Order.InverseLimitDomainWanted

open MathlibExt.Order.ScottContinuity.ContinuousLattice

universe u

open Set Topology Topology.WithScott

noncomputable section

variable {A B C : Type u} [CompleteLattice A] [CompleteLattice B] [CompleteLattice C]

private abbrev Maps (A B : Type u) [Preorder A] [Preorder B] :=
  {f : A → B // ScottContinuous f}

@[instance_reducible, local instance] private def mapsSupSet : SupSet (Maps A B) where
  sSup s := ⟨sSup (Subtype.val '' s),
    ScottContinuity.FunctionSpace.scottContinuous_sSup (by rintro _ ⟨f, _, rfl⟩; exact f.2)⟩

@[instance_reducible, local instance] private def mapsLattice : CompleteLattice (Maps A B) :=
  completeLatticeOfSup _ fun s =>
    ⟨fun f hf => le_sSup (s := Subtype.val '' s) ⟨f, hf, rfl⟩,
      fun g hg => sSup_le (s := Subtype.val '' s) (by rintro _ ⟨f, hf, rfl⟩; exact hg hf)⟩

private theorem maps_sSup_apply (s : Set (Maps A B)) (x : A) :
    (sSup s).1 x = ⨆ f ∈ s, f.val x := by
  change (sSup (Subtype.val '' s)) x = _
  rw [sSup_image]
  simp only [iSup_apply]

private theorem maps_iSup_apply {ι : Type*} (f : ι → Maps A B) (x : A) :
    (iSup f).1 x = ⨆ i, (f i).1 x := by
  rw [iSup, maps_sSup_apply, iSup_range]

private def eval (x : A) : sSupHom (Maps A B) B where
  toFun f := f.val x
  map_sSup' s := by rw [maps_sSup_apply, sSup_image]

private theorem scott (f : sSupHom A B) : ScottContinuous f :=
  .of_map_sSup fun _ _ _ => map_sSup f _

private def joinHom (f : A → B)
    (hf : ∀ {ι : Type u} (g : ι → A), f (iSup g) = ⨆ i, f (g i)) : sSupHom A B where
  toFun := f
  map_sSup' s := by rw [sSup_eq_iSup' s, hf, sSup_image, iSup_subtype']

private def composeMap {X Y : Type u} [CompleteLattice X] [CompleteLattice Y]
    (out : sSupHom B Y) (arg : sSupHom X A) : sSupHom (Maps A B) (Maps X Y) :=
  joinHom (fun f => ⟨out ∘ f.val ∘ arg, ((scott arg).comp f.2).comp (scott out)⟩)
    fun g => Subtype.ext (funext fun x => by
      simp only [Function.comp_apply, maps_iSup_apply, map_iSup])

-- An embedding-projection pair. In this tower both maps preserve arbitrary joins.
private structure Pair (A B : Type u) [CompleteLattice A] [CompleteLattice B] where
  emb : sSupHom A B
  proj : sSupHom B A
  retract (x : A) : proj (emb x) = x
  approx (y : B) : emb (proj y) ≤ y

private def basePair : Pair A (Maps A A) where
  emb := joinHom (fun x => ⟨Function.const A x, ScottContinuous.const x⟩)
    fun g => Subtype.ext (funext fun x => by rw [maps_iSup_apply]; rfl)
  proj := eval ⊥
  retract _ := rfl
  approx f x := f.2.monotone bot_le

private def Pair.lift (q : Pair A B) : Pair (Maps A A) (Maps B B) where
  emb := composeMap q.emb q.proj
  proj := composeMap q.proj q.emb
  retract f := Subtype.ext (funext fun x => by
    change q.proj (q.emb (f.val (q.proj (q.emb x)))) = _
    rw [q.retract, q.retract])
  approx f x := (q.approx _).trans (f.2.monotone (q.approx x))

-- Bundle the lattice with the carrier so iteration computes the order at successors as well.
private structure Stage where
  carrier : Type u
  [lattice : CompleteLattice carrier]

attribute [local instance] Stage.lattice

private def stage (A : Type u) [CompleteLattice A] : ℕ → Stage.{u}
  | 0 => ⟨A⟩
  | n + 1 => ⟨Maps (stage A n).carrier (stage A n).carrier⟩

private abbrev Level (A : Type u) [CompleteLattice A] (n : ℕ) := (stage A n).carrier

private def link (A : Type u) [CompleteLattice A] :
    (n : ℕ) → Pair (Level A n) (Level A (n + 1))
  | 0 => basePair
  | n + 1 => (link A n).lift

-- Scott-open neighborhoods yield finite joins of approximants and continuous step maps.
private def above (x : A) : Set (WithScott A) := interior {z | x ≤ ofScott z}

private theorem way_le {x y : A} (h : WayBelow x y) : x ≤ y := interior_subset h

private theorem way_from_map (p : A → B) (hp : ScottContinuous p) {x y : A} {b : B}
    (hb : WayBelow b (p y)) (h : ∀ z, b ≤ p z → x ≤ z) : WayBelow x y := by
  have hc : Continuous (fun z : WithScott A => toScott (p (ofScott z))) :=
    (IsScott.scottContinuousOn_iff_continuous (D := univ) (fun _ _ _ => trivial)).1
      (show ScottContinuousOn univ _ from hp.scottContinuousOn)
  exact interior_maximal (t := (fun z => toScott (p (ofScott z))) ⁻¹' above b)
    (fun z hz => h _ (interior_subset hz)) (isOpen_interior.preimage hc) hb

private theorem map_approximants (hA : IsContinuousLattice A) (f : A → B)
    (hf : ScottContinuous f) (x : A) :
    f x = ⨆ a ∈ {a | WayBelow a x}, f a := by
  let s := {a | WayBelow a x}
  have hne : s.Nonempty := ⟨⊥, interior_maximal (t := univ) (fun _ _ => bot_le)
    isOpen_univ trivial⟩
  have hd : DirectedOn (· ≤ ·) s := by
    intro a ha b hb
    refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
    exact interior_maximal (t := above a ∩ above b)
      (fun z hz => sup_le (interior_subset hz.1) (interior_subset hz.2))
      (isOpen_interior.inter isOpen_interior) ⟨ha, hb⟩
  exact (congrArg f (hA x)).trans ((hf.map_sSup hne hd).trans sSup_image)

private def step (a : A) (b : B) : Maps A B := by
  classical
  refine ⟨fun x => if WayBelow a x then b else ⊥, ?_⟩
  have hm : Monotone (fun x : A => if WayBelow a x then b else ⊥) := by
    intro x y hxy
    by_cases hx : WayBelow a x
    · have hy := (IsScott.isUpperSet_of_isOpen (D := univ)
          (show IsOpen (above a) from isOpen_interior)) (show toScott x ≤ toScott y from hxy) hx
      simp [hx, show WayBelow a y from hy]
    · simp [hx]
  intro s hs hd y hy
  refine ⟨hm.mem_upperBounds_image hy.1, fun z hz => ?_⟩
  by_cases h : WayBelow a y
  · obtain ⟨x, hx, hax⟩ :=
      (IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ)).1
        (show IsOpen (above a) from isOpen_interior) |>.2 (d := ofScott ⁻¹' s)
          trivial hs hd hy h
    simpa [h, show WayBelow a (ofScott x) from hax] using
      hz (mem_image_of_mem _ (show ofScott x ∈ s from hx))
  · simp [h]

-- If a is way below x and b is way below f(a), the step map is way below f
-- and takes value b at x. Taking both suprema recovers f(x).
private theorem maps_continuous (hA : IsContinuousLattice A) (hB : IsContinuousLattice B) :
    IsContinuousLattice (Maps A B) := by
  classical
  intro f
  refine le_antisymm ?_ (sSup_le fun g (hg : WayBelow g f) => way_le hg)
  intro x
  rw [map_approximants hA f.val f.2 x]
  refine iSup₂_le fun a ha => ?_
  conv_lhs => rw [hB (f.val a)]
  refine sSup_le fun b hb => ?_
  have hstep : WayBelow (step a b) f := by
    apply way_from_map (eval a) (scott (eval a)) hb
    intro g hg z
    change (if WayBelow a z then b else ⊥) ≤ g.val z
    split_ifs with haz
    · exact hg.trans (g.2.monotone (way_le haz))
    · exact bot_le
  have h := le_sSup (s := {g | WayBelow g f}) hstep x
  simpa [step, show WayBelow a x from ha] using h

private def Pair.ident : Pair A A :=
  ⟨sSupHom.id A, sSupHom.id A, fun _ => rfl, fun _ => le_rfl⟩

private def Pair.trans (q : Pair A B) (r : Pair B C) : Pair A C where
  emb := r.emb.comp q.emb
  proj := q.proj.comp r.proj
  retract x := by change q.proj (r.proj (r.emb (q.emb x))) = x; rw [r.retract, q.retract]
  approx y := (OrderHomClass.mono r.emb (q.approx _)).trans (r.approx y)

private def span {i j : ℕ} (h : i ≤ j) : Pair (Level A i) (Level A j) :=
  Nat.leRecOn (motive := fun k => Pair (Level A i) (Level A k)) h
    (fun {k} q => q.trans (link A k)) Pair.ident

private theorem span_self (n : ℕ) : span (A := A) (le_refl n) = Pair.ident := Nat.leRecOn_self _

private theorem span_succ {i j : ℕ} (h : i ≤ j) :
    span (A := A) (Nat.le_succ_of_le h) = (span h).trans (link A j) := Nat.leRecOn_succ h _

private theorem span_proj_first {i j : ℕ} (h : i + 1 ≤ j) (x : Level A j) :
    (span (Nat.le_of_succ_le h)).proj x = (link A i).proj ((span h).proj x) := by
  induction j, h using Nat.le_induction with
  | base => rw [span_succ (le_refl i), span_self, span_self]; rfl
  | succ j h ih =>
    rw [span_succ (Nat.le_of_succ_le h), span_succ h]
    exact ih ((link A j).proj x)

private abbrev Limit (A : Type u) [CompleteLattice A] :=
  {x : (n : ℕ) → Level A n // ∀ n, (link A n).proj (x (n + 1)) = x n}

@[instance_reducible, local instance] private def limitSupSet : SupSet (Limit A) where
  sSup s := ⟨fun n => ⨆ x ∈ s, x.val n, fun n => by
    simp only [map_iSup]
    exact iSup_congr fun x => iSup_congr fun _ => x.property n⟩

@[instance_reducible, local instance] private def limitLattice : CompleteLattice (Limit A) :=
  completeLatticeOfSup _ fun s =>
    ⟨fun x hx n => le_iSup₂ (f := fun (y : Limit A) (_ : y ∈ s) => y.val n) x hx,
      fun _ hy n => iSup₂_le fun _ hx => hy hx n⟩

private def coord (n : ℕ) : sSupHom (Limit A) (Level A n) where
  toFun x := x.val n
  map_sSup' _ := sSup_image.symm

-- Transport a level in both directions. The two branches agree on the diagonal.
private def transport (n k : ℕ) : sSupHom (Level A n) (Level A k) :=
  if h : n ≤ k then (span h).emb else (span (Nat.le_of_lt (Nat.lt_of_not_ge h))).proj

private theorem transport_self (n : ℕ) (x : Level A n) : transport n n x = x := by
  simp only [transport, dite_eq_left le_rfl, span_self]; rfl

private theorem transport_coherent (n k : ℕ) (x : Level A n) :
    (link A k).proj (transport n (k + 1) x) = transport n k x := by
  rcases le_or_gt n k with h | h
  · simp only [transport, dite_eq_left h, dite_eq_left (Nat.le_succ_of_le h), span_succ h]
    exact (link A k).retract _
  · rcases Nat.eq_or_lt_of_le h with he | hl
    · subst n
      rw [transport_self, transport, dite_eq_right (by omega), span_succ (le_refl k), span_self]
      rfl
    · rw [transport, dite_eq_right (by omega), transport, dite_eq_right (by omega)]
      exact (span_proj_first h x).symm

private def incl (n : ℕ) : sSupHom (Level A n) (Limit A) :=
  joinHom (fun x => ⟨fun k => transport n k x, fun k => transport_coherent n k x⟩)
    fun g => Subtype.ext (funext fun k => by
      change transport n k (iSup g) = coord k (iSup _)
      rw [map_iSup, map_iSup]; rfl)

private theorem proj_incl (n : ℕ) (x : Level A n) : coord n (incl n x) = x := transport_self n x

private theorem span_proj_coord {n k : ℕ} (h : n ≤ k) (x : Limit A) :
    (span h).proj (coord k x) = coord n x := by
  induction k, h using Nat.le_induction with
  | base => rw [span_self]; rfl
  | succ k h ih =>
    rw [span_succ h]
    change (span h).proj ((link A k).proj (x.val (k + 1))) = _
    rw [x.property, ← ih]; rfl

private theorem incl_proj_le (n : ℕ) (x : Limit A) : incl n (coord n x) ≤ x := by
  intro k
  change transport n k (coord n x) ≤ coord k x
  unfold transport
  split_ifs with h
  · rw [← span_proj_coord h x]
    exact (span h).approx _
  · exact (span_proj_coord _ x).le

private theorem incl_le_iff (n : ℕ) (a : Level A n) (x : Limit A) :
    incl n a ≤ x ↔ a ≤ coord n x :=
  ⟨fun h => proj_incl n a ▸ OrderHomClass.mono (coord n) h,
    fun h => (OrderHomClass.mono (incl n) h).trans (incl_proj_le n x)⟩

private theorem coord_succ (n : ℕ) (x : Limit A) :
    (link A n).proj (coord (n + 1) x) = coord n x := x.property n

private theorem incl_succ (n : ℕ) (a : Level A n) :
    incl (n + 1) ((link A n).emb a) = incl n a := by
  apply eq_of_forall_ge_iff
  intro x
  rw [incl_le_iff, incl_le_iff, ← coord_succ n x]
  exact ⟨fun h => (link A n).retract a ▸ OrderHomClass.mono (link A n).proj h,
    fun h => (OrderHomClass.mono (link A n).emb h).trans ((link A n).approx _)⟩

private def approxAt (n : ℕ) (x : Limit A) := incl n (coord n x)

private theorem approx_mono (x : Limit A) : Monotone fun n => approxAt n x := by
  apply monotone_nat_of_le_succ
  intro n
  unfold approxAt
  rw [← incl_succ, ← coord_succ n x]
  exact OrderHomClass.mono _ ((link A n).approx _)

-- At coordinate n the nth approximation has already attained the required value.
private theorem approx_sup (x : Limit A) : (⨆ n, approxAt n x) = x := by
  refine le_antisymm (iSup_le fun n => incl_proj_le n x) fun n => ?_
  calc
    coord n x = coord n (approxAt n x) := (proj_incl n _).symm
    _ ≤ _ := OrderHomClass.mono (coord n) (le_iSup (fun k => approxAt k x) n)

private theorem level_continuous (hA : IsContinuousLattice A) :
    ∀ n, IsContinuousLattice (Level A n)
  | 0 => hA
  | n + 1 => maps_continuous (level_continuous hA n) (level_continuous hA n)

private theorem limit_continuous (hA : IsContinuousLattice A) : IsContinuousLattice (Limit A) := by
  intro x
  refine le_antisymm ?_ (sSup_le fun y (hy : WayBelow y x) => way_le hy)
  conv_lhs => rw [← approx_sup x]
  refine iSup_le fun n => ?_
  unfold approxAt
  rw [level_continuous hA n (coord n x), map_sSup, sSup_image]
  refine iSup₂_le fun a ha => le_sSup (s := {y | WayBelow y x}) ?_
  exact way_from_map (coord n) (scott (coord n)) ha fun y => (incl_le_iff n a y).2

-- Restrict an endomap to a finite level, or extend a level endomap to the whole limit.
private def restrictMap (n : ℕ) : sSupHom (Maps (Limit A) (Limit A)) (Level A (n + 1)) :=
  composeMap (coord n) (incl n)

private def extendMap (n : ℕ) : sSupHom (Level A (n + 1)) (Maps (Limit A) (Limit A)) :=
  composeMap (incl n) (coord n)

private theorem restrict_coherent (n : ℕ) (f : Maps (Limit A) (Limit A)) :
    (link A (n + 1)).proj (restrictMap (n + 1) f) = restrictMap n f := by
  apply Subtype.ext
  funext a
  change (link A n).proj (coord (n + 1) (f.val (incl (n + 1) ((link A n).emb a)))) = _
  rw [incl_succ, coord_succ]; rfl

private def encode (f : Maps (Limit A) (Limit A)) : Limit A :=
  ⟨fun n => match n with
    | 0 => (link A 0).proj (restrictMap 0 f)
    | n + 1 => restrictMap n f,
    fun n => by cases n with
      | zero => rfl
      | succ n => exact restrict_coherent n f⟩

private def decode (x : Limit A) : Maps (Limit A) (Limit A) :=
  ⨆ n, extendMap n (coord (n + 1) x)

private theorem encode_mono :
    Monotone (encode (A := A)) := by
  intro f g h n
  cases n with
  | zero => exact OrderHomClass.mono (link A 0).proj (OrderHomClass.mono (restrictMap 0) h)
  | succ n => exact OrderHomClass.mono (restrictMap n) h

private theorem decode_mono :
    Monotone (decode (A := A)) := fun _ _ h =>
  iSup_mono fun n => OrderHomClass.mono (extendMap n) (h (n + 1))

private theorem extend_mono (x : Limit A) : Monotone fun n => extendMap n (coord (n + 1) x) := by
  apply monotone_nat_of_le_succ
  intro n y
  let g : Maps (Level A (n + 1)) (Level A (n + 1)) := coord (n + 2) x
  change incl n ((coord (n + 1) x).val (coord n y)) ≤ incl (n + 1) (g.val (coord (n + 1) y))
  have h (a : Level A n) :
      (coord (n + 1) x).val a = (link A n).proj (g.val ((link A n).emb a)) :=
    congrArg (fun f : Level A (n + 1) => f.val a) (coord_succ (n + 1) x).symm
  rw [h, ← incl_succ, ← coord_succ n y]
  exact OrderHomClass.mono (incl (n + 1))
    (((link A n).approx _).trans (g.2.monotone ((link A n).approx _)))

private theorem restrict_extend (n : ℕ) (g : Level A (n + 1)) :
    restrictMap n (extendMap n g) = g :=
  Subtype.ext (funext fun a => by
    change coord n (incl n (g.val (coord n (incl n a)))) = _
    rw [proj_incl, proj_incl])

private theorem restrict_extend_above (x : Limit A) {k m : ℕ} (h : k ≤ m) :
    restrictMap k (extendMap m (coord (m + 1) x)) = coord (k + 1) x := by
  let f := extendMap m (coord (m + 1) x)
  have hm : coord (m + 1) (encode f) = coord (m + 1) x := restrict_extend m _
  calc
    _ = (span (Nat.succ_le_succ h)).proj (coord (m + 1) (encode f)) :=
      (span_proj_coord _ (encode f)).symm
    _ = _ := hm ▸ span_proj_coord (Nat.succ_le_succ h) x

private theorem restrict_decode (x : Limit A) (k : ℕ) :
    restrictMap k (decode x) = coord (k + 1) x := by
  rw [decode, map_iSup]
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rcases le_total k m with h | h
    · exact (restrict_extend_above x h).le
    · exact (OrderHomClass.mono (restrictMap k) (extend_mono x h)).trans (restrict_extend k _).le
  · exact le_iSup_of_le k (restrict_extend k _).ge

private theorem encode_decode (x : Limit A) : encode (decode x) = x := by
  apply Subtype.ext
  funext n
  cases n with
  | zero =>
    change (link A 0).proj (restrictMap 0 (decode x)) = _
    rw [restrict_decode, coord_succ]; rfl
  | succ n => exact restrict_decode x n

private theorem map_approx_sup (f : Maps (Limit A) (Limit A)) (y : Limit A) :
    f.val y = ⨆ n, f.val (approxAt n y) := by
  let a (n : ℕ) := approxAt n y
  have hd : Directed (· ≤ ·) a := (approx_mono y).directed_le
  calc
    f.val y = f.val (iSup a) := congrArg f.val (approx_sup y).symm
    _ = sSup (f.val '' range a) := f.2.map_sSup (range_nonempty a) hd.directedOn_range
    _ = _ := by rw [← range_comp]; rfl

private theorem decode_encode (f : Maps (Limit A) (Limit A)) : decode (encode f) = f := by
  apply Subtype.ext
  funext y
  rw [decode, maps_iSup_apply]
  change (⨆ n, approxAt n (f.val (approxAt n y))) = f.val y
  refine le_antisymm (iSup_le fun n => (incl_proj_le n _).trans (f.2.monotone (incl_proj_le n y)))
    ?_
  -- Approximate the argument at stage i and the value at stage j. The stage max i j
  -- bounds both approximations and occurs in the diagonal supremum.
  conv_lhs => rw [map_approx_sup f y]
  refine iSup_le fun i => ?_
  conv_lhs => rw [← approx_sup (f.val (approxAt i y))]
  refine iSup_le fun j => le_iSup_of_le (max i j) ?_
  apply (approx_mono _ (le_max_right i j)).trans
  exact OrderHomClass.mono (incl _) (OrderHomClass.mono (coord _)
    (f.2.monotone (approx_mono y (le_max_left i j))))

private def limitIso : Limit A ≃o Maps (Limit A) (Limit A) where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode
  map_rel_iff' := by
    intro x y
    change decode x ≤ decode y ↔ x ≤ y
    exact ⟨fun h => by simpa only [encode_decode] using encode_mono h, fun h => decode_mono h⟩

/-- **Scott's inverse-limit theorem.** The domain equation `D ≅ [D → D]` has non-trivial
solutions among continuous lattices. For every continuous lattice `D₀` there is a continuous
lattice `D` that is order-isomorphic to the lattice of its own Scott-continuous self-maps, ordered
pointwise, and of which `D₀` is a projection: there are Scott-continuous `e : D₀ → D` and
`p : D → D₀` with `p ∘ e = id` and `e ∘ p ≤ id` (D. Scott, *Continuous Lattices*, Oxford PRG-7
(1971), Proposition 4.1, Proposition 4.2 and Theorem 4.4, with continuous lattices as in
Definition 2.3 and projections as in Definition 3.6). If `D₀` has two distinct elements, so has
`D`, because `e` is injective.

The hypotheses are Scott's. The statement asserts only that such a `D` exists, while Scott
constructs a specific one, `D∞`, from a chosen projection pair between `D₀` and `[D₀ → D₀]`.
Scott states a homeomorphism for the induced topologies; an order isomorphism between complete
lattices is a homeomorphism for their Scott topologies, and for continuous lattices Scott shows
that the topology of `[D → D]` is its Scott topology (Theorem 3.3), so the order isomorphism
carries the same information. -/
theorem exists_orderIso_scottContinuous_self (D₀ : Type u) [CompleteLattice D₀]
    (h₀ : IsContinuousLattice D₀) :
    ∃ (D : Type u) (_ : CompleteLattice D) (_ : D ≃o {f : D → D // ScottContinuous f})
      (e : D₀ → D) (p : D → D₀),
      IsContinuousLattice D ∧ ScottContinuous e ∧ ScottContinuous p ∧ p ∘ e = id ∧ e ∘ p ≤ id := by
  exact ⟨Limit D₀, limitLattice, limitIso, incl 0, coord 0, limit_continuous h₀,
    scott (incl 0), scott (coord 0), funext (proj_incl 0), incl_proj_le 0⟩

end

end MathlibExt.Order.InverseLimitDomainWanted

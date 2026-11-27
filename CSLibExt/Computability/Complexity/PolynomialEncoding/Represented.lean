/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Enumerate
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import CSLibExt.Computability.Complexity.BoolClosure

/-!
# Polynomial-time computations on represented data

A witness computes on every raw input within polynomial time. Its specification need
only describe valid input representations. This permits nested scoped comprehensions.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Comprehension

open MetaMathlibExt BitstringEncoding ComplexityTheory BitScan

local notation "Bits" => List Bool

/-- Rows of a list under the stated element representation. -/
def frames {α : Type} (e : α → Bits) (xs : List α) : Bits := (xs.map e).flatMap delimit

theorem frames_encode {α : Type} [BitstringEncoding α] (xs : List α) :
    frames bitEncode xs = bitEncode xs := by
  change (xs.map bitEncode).flatMap delimit = ((xs.map bitEncode).map delimit).flatten
  rw [List.flatMap_def]

/-- Representation of a product with a self-delimiting left field. -/
def pair {α β : Type} (a : α → Bits) (b : β → Bits) (p : α × β) := pack (a p.1) (b p.2)

/-- An everywhere polynomial-time implementation on bitstrings, correct on representations. -/
def Represented {α : Type} (e f : α → Bits) : Prop :=
  ∃ run : Bits → Bits, IsPolyTime run ∧ ∀ a, run (e a) = f a

theorem polyId : IsPolyTime (fun x : Bits => x) := by
  let s (_ : Unit) (b : Bool) : Unit × Bits := ((), [b])
  have hh (x : Bits) : scan s (fun _ => []) () x = x := by
    induction x with
    | nil => rfl
    | cons b x ih => simp [scan, s, ih]
  exact (funext hh) ▸ polyScan s (fun _ => []) ()

namespace Represented

variable {α β γ : Type} {e : α → Bits} {r : β → Bits} {f g h : α → Bits}

theorem input (e : α → Bits) : Represented e e := ⟨id, polyId, fun _ => rfl⟩

theorem const (e : α → Bits) (s : Bits) : Represented e (fun _ => s) :=
  ⟨_, polyConst s, fun _ => rfl⟩

theorem transport (hf : Represented e f) (eqn : ∀ a, f a = g a) : Represented e g := by
  obtain ⟨run, hr, h⟩ := hf
  exact ⟨run, hr, fun a => (h a).trans (eqn a)⟩

theorem after (hf : Represented e f) {t : Bits → Bits} (ht : IsPolyTime t) :
    Represented e (fun a => t (f a)) := by
  obtain ⟨run, hr, h⟩ := hf
  exact ⟨_, hr.comp ht, fun a => congrArg t (h a)⟩

theorem append (hf : Represented e f) (hg : Represented e g) :
    Represented e (fun a => f a ++ g a) := by
  obtain ⟨sf, pf, ef⟩ := hf
  obtain ⟨sg, pg, eg⟩ := hg
  exact ⟨_, polyAppend pf pg, fun a => by simp [ef, eg]⟩

theorem packed (hf : Represented e f) (hg : Represented e g) :
    Represented e (fun a => pack (f a) (g a)) := by
  obtain ⟨sf, pf, ef⟩ := hf
  obtain ⟨sg, pg, eg⟩ := hg
  exact ⟨_, polyPack pf pg, fun a => by simp [ef, eg]⟩

theorem frame (hf : Represented e f) : Represented e (fun a => delimit (f a)) :=
  hf.after polyDelimit

theorem fst (r : β → Bits) (hf : Represented e f) :
    Represented (pair e r) (fun p => f p.1) := by
  obtain ⟨sf, pf, ef⟩ := hf
  exact ⟨_, (polyField true false).comp pf, fun p => by
    change sf (hd (pack (e p.1) (r p.2))) = _
    rw [hd_pack, ef]⟩

theorem snd (r : β → Bits) (hf : Represented e f) :
    Represented (pair r e) (fun p => f p.2) := by
  obtain ⟨sf, pf, ef⟩ := hf
  exact ⟨_, (polyField false true).comp pf, fun p => by
    change sf (tl (pack (r p.1) (e p.2))) = _
    rw [tl_pack, ef]⟩

theorem cond {pred : α → Bool} (hp : Represented e (fun x => [pred x]))
    (hf : Represented e f) (hg : Represented e g) :
    Represented e (fun a => if pred a then f a else g a) := by
  obtain ⟨sp, pp, ep⟩ := hp
  obtain ⟨sf, pf, ef⟩ := hf
  obtain ⟨sg, pg, eg⟩ := hg
  let yes (x : Bits) := (sp x).head?.getD false
  let s (q : Option Bool) (b : Bool) : Option Bool × Bits := (some (q.getD b), [])
  have run (v : Option Bool) (xs : Bits) : scan s (fun q => [q.getD false]) v xs =
      [v.getD (xs.head?.getD false)] := by
    induction xs generalizing v with
    | nil => rfl
    | cons b xs ih => simp [scan, s, ih]
  have py : IsPolyTime (fun x => [yes x]) := by
    have := pp.comp (polyScan s (fun q => [q.getD false]) none)
    simpa [Function.comp_def, yes, run] using this
  exact ⟨_, polyIf py pf pg, fun a => by simp [yes, ep, ef, eg]⟩

theorem test₂ {t : Bits × Bits → Bool} (ht : IsPolyTime t)
    (hf : Represented e f) (hg : Represented e g) :
    Represented e (fun x => [t (f x, g x)]) := by
  obtain ⟨sf, pf, ef⟩ := hf
  obtain ⟨sg, pg, eg⟩ := hg
  exact ⟨_, ((polyPair pf pg).comp ht).comp isPolyTime_singleton,
    fun a => by simp [Function.comp_def, ef, eg]⟩

theorem flatMap {rows : α → List β} {body : β × α → Bits}
    (rs : Represented e (fun x => frames r (rows x))) (bs : Represented (pair r e) body) :
    Represented e (fun a => (rows a).flatMap (fun b => body (b, a))) := by
  obtain ⟨sf, pf, ef⟩ := rs
  obtain ⟨sg, pg, eg⟩ := bs
  refine ⟨_, polyFlatMap pf polyId pg, ?_⟩
  intro a
  simp only [ef, frames, rowsOf_frames]
  rw [List.flatMap_map]
  change (rows a).flatMap (fun b => sg (pair r e (b, a))) = _
  simp only [eg]

theorem map {rows : α → List β} {body : β × α → Bits}
    (rs : Represented e (fun x => frames r (rows x))) (bs : Represented (pair r e) body) :
    Represented e (fun a => frames id ((rows a).map (fun b => body (b, a)))) :=
  (rs.flatMap bs.frame).transport (fun a => by simp [frames, List.flatMap_map])

theorem count {rows : α → List β} (rs : Represented e (fun x => frames r (rows x))) :
    Represented e (fun a => unary (rows a).length) := by
  apply (rs.flatMap (const _ [true])).transport
  intro a
  induction rows a with
  | nil => rfl
  | cons b xs ih => simp [unary, List.replicate_succ, ih]

/-- Representation of (payload, index) that puts the unary index first. -/
def numbered (r : β → Bits) (p : β × ℕ) := pack (unary p.2) (r p.1)

theorem enumerate {rows : α → List β} (rs : Represented e (fun x => frames r (rows x))) :
    Represented e (fun a => frames (numbered r) (rows a).zipIdx) := by
  obtain ⟨sf, pf, ef⟩ := rs
  refine ⟨_, polyEnumerate pf, ?_⟩
  intro a
  simp only [ef, frames, rowsOf_frames]
  congr 1
  generalize rows a = xs
  generalize (0 : ℕ) = i
  induction xs generalizing i with
  | nil => rfl
  | cons b xs ih =>
    change (pack (unary i) (r b) :: indexed (xs.map r) (i + 1)) =
      pack (unary i) (r b) :: (xs.zipIdx (i + 1)).map (numbered r)
    rw [ih]

theorem neg {p : α → Bool} (hp : Represented e (fun a => [p a])) :
    Represented e (fun a => [!p a]) :=
  (hp.cond (const _ [false]) (const _ [true])).transport (by intro a; cases p a <;> rfl)

theorem both {p q : α → Bool} (hp : Represented e (fun a => [p a]))
    (hq : Represented e (fun a => [q a])) : Represented e (fun a => [p a && q a]) :=
  (hp.cond hq (const _ [false])).transport (by intro a; cases p a <;> rfl)

theorem testAny {rows : α → List β} {p : β × α → Bool}
    (rs : Represented e (fun x => frames r (rows x)))
    (hp : Represented (pair r e) (fun x => [p x])) :
    Represented e (fun x => [(rows x).any (fun b => p (b,x))]) := by
  have flags := rs.flatMap (hp.cond (const _ [true]) (const _ []))
  apply (flags.after polyEmpty).neg.transport
  intro x
  induction rows x with
  | nil => rfl
  | cons a xs ih => cases h : p (a,x) <;> simp_all

theorem filtered {rows : α → List β} {p : β × α → Bool}
    (rs : Represented e (fun x => frames r (rows x)))
    (hp : Represented (pair r e) (fun x => [p x])) :
    Represented e (fun x => frames r ((rows x).filter (fun b => p (b,x)))) := by
  have elem := (input r).fst e
  apply (rs.flatMap (hp.cond elem.frame (const _ []))).transport
  intro x
  induction rows x with
  | nil => rfl
  | cons a xs ih => cases h : p (a,x) <;> simp_all [frames]

theorem mapped {t : γ → Bits} {rows : α → List β} {body : β × α → γ}
    (rs : Represented e (fun x => frames r (rows x)))
    (bs : Represented (pair r e) (fun p => t (body p))) :
    Represented e (fun a => frames t ((rows a).map (fun b => body (b, a)))) :=
  (rs.flatMap bs.frame).transport (by intro a; simp [frames, List.flatMap_map])

theorem join {rows more : α → List β} (rs : Represented e (fun x => frames r (rows x)))
    (ts : Represented e (fun x => frames r (more x))) :
    Represented e (fun x => frames r (rows x ++ more x)) :=
  (rs.append ts).transport (by simp [frames])

end Represented

end Cslib.Complexity.PolynomialEncoding.Comprehension

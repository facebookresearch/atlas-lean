/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Comprehension
public import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import CSLibExt.Computability.CookLevin

/-!
# Compositional machine certificates for partial bitstring decoders

The generic product and list instances normalize arbitrary accepted words
to their canonical encodings. The independent validity bit covers every
malformed raw word, including a truncated outer or nested frame.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding

open MetaMathlibExt BitstringEncoding ComplexityTheory BitScan Comprehension

local notation "Bits" => List Bool

/-- An actual polynomial-time decoder certificate for ATLAS's canonical serialization. -/
structure CodecMachine (α : Type) [BitstringEncoding α] where
  normalize : Bits → Bits
  valid : Bits → Bool
  polyNormalize : IsPolyTime normalize
  polyValid : IsPolyTime (fun x => [valid x])
  valid_eq (x : Bits) : valid x = (bitDecode (α := α) x).isSome
  normalize_eq {x : Bits} {a : α} : bitDecode x = some a → normalize x = bitEncode a

namespace CodecMachine

/-- The first complete delimiter may be followed by arbitrary raw bits. -/
theorem polyFirstValid : IsPolyTime (fun x : Bits => [(undelimit x).isSome]) := by
  let finish (q : Option Bool) := [q.isNone]
  have rest (x : Bits) : scan (splitStep false false) finish none x = [true] := by
    induction x with
    | nil => rfl
    | cons b x ih => exact ih
  have h (x : Bits) :
      scan (splitStep false false) finish (some false) x = [(undelimit x).isSome] := by
    induction x using undelimit.induct with
    | case1 xs => exact rest xs
    | case2 b xs ih =>
      change scan _ _ (some false) xs = [((undelimit xs).map _).isSome]
      simpa using ih
    | case3 x h₁ h₂ =>
      cases x with
      | nil => rfl
      | cons b xs =>
        cases b with
        | false => exact (h₁ xs rfl).elim
        | true =>
          cases xs with
          | nil => rfl
          | cons c xs => exact (h₂ c xs rfl).elim
  exact (funext h) ▸ polyScan _ _ (some false)

/-- All raw natural-number payloads decode, including ones with an implicit high bit. -/
def nat : CodecMachine ℕ where
  normalize := FramedCNF.normalizeNat
  valid := fun _ => true
  polyNormalize := FramedCNF.NormalizeMachine.isPolyTime_normalizeNat
  polyValid := polyConst [true]
  valid_eq _ := rfl
  normalize_eq := by
    intro x a h
    change some (Computability.decodeNat x) = some a at h
    cases h
    exact FramedCNF.normalizeNat_eq_encode_decode x

private theorem product_decode {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (x : Bits) : bitDecode (α := α × β) x =
      (match undelimit x with
       | none => none
       | some (p, r) =>
         match bitDecode (α := α) p, bitDecode (α := β) r with
         | some a, some b => some (a, b) | _, _ => none) := rfl

private theorem product_frame {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p r : Bits) : bitDecode (α := α × β) (pack p r) =
      (match bitDecode (α := α) p, bitDecode (α := β) r with
       | some a, some b => some (a, b) | _, _ => none) := by
  rw [product_decode]
  simp only [pack, undelimit_delimit]

/-- Decode and validate both components of a framed product. -/
def prod {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (A : CodecMachine α) (B : CodecMachine β) : CodecMachine (α × β) where
  normalize x := pack (A.normalize (hd x)) (B.normalize (tl x))
  valid x := (undelimit x).isSome && A.valid (hd x) && B.valid (tl x)
  polyNormalize := polyPack ((polyField true false).comp A.polyNormalize)
    ((polyField false true).comp B.polyNormalize)
  polyValid := polyBool3 (fun a b c => a && b && c) polyFirstValid
    ((polyField true false).comp A.polyValid) ((polyField false true).comp B.polyValid)
  valid_eq x := by
    cases h : undelimit x with
    | none => rw [product_decode, h]; rfl
    | some q =>
      obtain ⟨p,r⟩ := q
      obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp h
      change (true && A.valid (hd (pack p r)) && B.valid (tl (pack p r))) =
        (bitDecode (α := α × β) (pack p r)).isSome
      rw [hd_pack, tl_pack, A.valid_eq, B.valid_eq, product_frame]
      cases bitDecode (α := α) p <;> cases bitDecode (α := β) r <;> rfl
  normalize_eq := by
    intro x q h
    cases e : undelimit x with
    | none => rw [product_decode, e] at h; cases h
    | some a =>
      obtain ⟨p,r⟩ := a
      obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).mp e
      change bitDecode (pack p r) = some q at h
      rw [product_frame] at h
      cases hp : bitDecode (α := α) p <;> cases hr : bitDecode (α := β) r <;>
        simp_all only [reduceCtorEq]
      obtain rfl := Option.some.inj h
      change pack (A.normalize (hd (pack p r))) (B.normalize (tl (pack p r))) = _
      rw [hd_pack, tl_pack, A.normalize_eq hp, B.normalize_eq hr]
      rfl

/-- A nonempty rejection word records at least one invalid element payload. -/
def rejects {α : Type} [BitstringEncoding α] (A : CodecMachine α) (rs : List Bits) : Bits :=
  rs.flatMap fun p => if A.valid p then [] else [true]

private theorem rejects_eq {α : Type} [BitstringEncoding α] (A : CodecMachine α) (rs : List Bits) :
    (rejects A rs).isEmpty = (rs.mapM (bitDecode (α := α))).isSome := by
  induction rs with
  | nil => rfl
  | cons p ps ih =>
    change ((if A.valid p then [] else [true]) ++ rejects A ps).isEmpty = _
    rw [List.mapM_cons, A.valid_eq]
    cases hp : bitDecode (α := α) p <;> cases hps : ps.mapM (bitDecode (α := α)) <;>
      simp_all [Option.bind]

private theorem norm_rows {α : Type} [BitstringEncoding α] (A : CodecMachine α)
    (rs : List Bits) {l : List α} (h : rs.mapM (bitDecode (α := α)) = some l) :
    (rs.flatMap fun p => delimit (A.normalize p)) = bitEncode l := by
  induction rs generalizing l with
  | nil =>
    have he : some ([] : List α) = some l := h
    cases he
    rfl
  | cons p ps ih =>
    rw [List.mapM_cons] at h
    obtain ⟨a, hp, hh⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨as, hs, hh'⟩ := Option.bind_eq_some_iff.mp hh
    have he : some (a :: as) = some l := hh'
    cases he
    change delimit (A.normalize p) ++ _ = delimit (bitEncode a) ++ bitEncode as
    rw [A.normalize_eq hp]
    exact congrArg (delimit (bitEncode a) ++ ·) (ih hs)

/-- Validate the complete outer row framing and all recursively decoded elements. -/
def list {α : Type} [BitstringEncoding α] (A : CodecMachine α) : CodecMachine (List α) where
  normalize x := (rowsOf x).flatMap fun p => delimit (A.normalize p)
  valid x := (undelimitBlocks x).isSome && (rejects A (rowsOf x)).isEmpty
  polyNormalize := by
    have run := polyFlatMap polyWordId (polyConst [])
      (((polyField true false).comp A.polyNormalize).comp polyDelimit)
    simpa only [hd_pack, Function.comp_def] using run
  polyValid := by
    have r := polyFlatMap polyWordId (polyConst [])
      (polyIf ((polyField true false).comp A.polyValid) (polyConst []) (polyConst [true]))
    have hr : IsPolyTime (fun x => rejects A (rowsOf x)) := by
      simpa only [rejects, hd_pack, Function.comp_def] using r
    exact polyBool3 (fun a b _ => a && b) polyFramesValid (hr.comp polyEmpty) (polyConst [false])
  valid_eq x := by
    change _ = ((undelimitBlocks x).bind (List.mapM (bitDecode (α := α)))).isSome
    cases h : undelimitBlocks x with
    | none => rfl
    | some rs => simpa [rowsOf, h] using rejects_eq A rs
  normalize_eq := by
    intro x l h
    change (undelimitBlocks x).bind (List.mapM (bitDecode (α := α))) = some l at h
    obtain ⟨rs, hrs, h⟩ := Option.bind_eq_some_iff.mp h
    simpa only [rowsOf, hrs, Option.getD_some] using norm_rows A rs h

end CodecMachine

end Cslib.Complexity.PolynomialEncoding

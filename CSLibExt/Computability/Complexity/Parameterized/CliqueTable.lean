/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.CliqueMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import CSLibExt.Computability.Complexity.PolynomialEncoding.RowDedup
import CSLibExt.Computability.Complexity.PolynomialEncoding.CodecMachine

/-!
# The compact vertex and incompatibility tables for Clique
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CliqueMembership

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding PolynomialEncoding.Comprehension

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "E" => (bitEncode (α := ℕ × ℕ))
local notation "V" => (Represented.numbered N)

private theorem injectiveEncode {A : Type} [BitstringEncoding A] :
    Function.Injective (bitEncode (α := A)) := by
  intro x y h
  exact Option.some.inj (by simpa using congrArg (bitDecode (α := A)) h)

private theorem ltRep {D : Type} {e : D → Bits} {a b : D → ℕ}
    (ha : Represented e (fun x => N (a x)))
    (hb : Represented e (fun x => N (b x))) : Represented e (fun x => [decide (a x < b x)]) := by
  apply (hb.test₂ BitZip.polyDecodedLE ha).neg.transport
  intro x
  change [!decide (Computability.decodeNat (Computability.encodeNat _) ≤
    Computability.decodeNat (Computability.encodeNat _))] = _
  by_cases h : a x < b x
  · simp [Computability.decode_encodeNat, h, Nat.not_le_of_gt h]
  · simp [Computability.decode_encodeNat, h, Nat.le_of_not_gt h]

private theorem valV : Represented V (fun p => N p.1) :=
  ⟨_, BitScan.polyField false true, by intro p; exact tl_pack (unary p.2) (N p.1)⟩

private theorem indexV : Represented V (fun p => N p.2) := by
  have unaryIndex : Represented V (fun p => unary p.2) :=
    ⟨_, BitScan.polyField true false, by intro p; exact hd_pack (unary p.2) (N p.1)⟩
  exact (unaryIndex.after isPolyTime_encodeLength).transport (by simp)

/-- Build the compact vertex table, discarding out-of-range endpoints and keeping a representative
for singleton cliques in nonempty graphs. Index comparisons use normalized binary naturals. -/
theorem represented_vertices {D : Type} {e : D → Bits} {n : D → ℕ} {edges : D → List (ℕ × ℕ)}
    (hn : Represented e (fun x => N (n x))) (he : Represented e (fun x => frames E (edges x))) :
    Represented e (fun x => frames N (vertices (n x) (edges x))) := by
  have fst : Represented E (fun p => N p.1) := (Represented.input N).fst N
  have snd : Represented E (fun p => N p.2) := (Represented.input N).snd N
  have endpoints := (he.mapped (fst.fst e)).join (he.mapped (snd.fst e))
  have inRange := endpoints.filtered (ltRep ((Represented.input N).fst e) (hn.snd N))
  have z : Represented e (fun x => frames N (List.range (min 1 (n x)))) := by
    have hpos := ltRep (Represented.const e (N 0)) hn
    apply (hpos.cond (Represented.const e (frames N [0])) (Represented.const e [])).transport
    intro x
    cases n x <;> rfl
  exact Represented.dedup injectiveEncode (z.join inRange)


private theorem indexRows (vs : List ℕ) :
    vs.zipIdx = (List.range vs.length).map (fun i => (vs.getD i 0, i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < vs.length := by simpa using h₁
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private def forbidden (es : List (ℕ × ℕ)) (a b : ℕ × ℕ) :=
  decide (a.2 ≠ b.2 ∧ (a.1,b.1) ∉ es ∧ (b.1,a.1) ∉ es)

private theorem forbiddenRows (vs : List ℕ) (es : List (ℕ × ℕ)) :
    vs.zipIdx.flatMap (fun a =>
      (vs.zipIdx.filter (forbidden es a)).map (fun b => (a.2,b.2))) = forbiddenPairs vs es := by
  rw [indexRows]
  simp only [forbiddenPairs, forbidden, List.product, List.flatMap_map,
    List.filter_flatMap, List.filter_map, List.map_map, Function.comp_def]

/-- Enumerate the Cartesian square of the compact vertices and emit precisely the missing edges
between different indices, checking both orientations of each listed input edge. -/
theorem represented_forbiddenPairs {D : Type} {e : D → Bits}
    {vs : D → List ℕ} {es : D → List (ℕ × ℕ)}
    (hv : Represented e (fun x => frames N (vs x)))
    (he : Represented e (fun x => frames E (es x))) :
    Represented e (fun x => frames E (forbiddenPairs (vs x) (es x))) := by
  let p := pair V e
  let q := pair V p
  have rs := hv.enumerate
  have u : Represented q (fun d => N d.2.1.1) := (valV.fst e).snd V
  have v : Represented q (fun d => N d.1.1) := valV.fst p
  have i : Represented q (fun d => N d.2.1.2) := (indexV.fst e).snd V
  have j : Represented q (fun d => N d.1.2) := indexV.fst p
  have edges : Represented q (fun d => frames E (es d.2.2)) := (he.snd V).snd V
  have uv : Represented q (fun d => E (d.2.1.1, d.1.1)) := u.packed v
  have vu : Represented q (fun d => E (d.1.1, d.2.1.1)) := v.packed u
  have absEdge (f : (ℕ × ℕ) × ((ℕ × ℕ) × D) → ℕ × ℕ)
      (hf : Represented q (fun d => E (f d))) :
      Represented q (fun d => [decide (f d ∉ es d.2.2)]) := by
    have test := Represented.equal injectiveEncode ((Represented.input E).fst q) (hf.snd E)
    apply (edges.testAny test).neg.transport
    intro d
    simp only [decide_not, List.cons.injEq, Bool.not_eq_eq_eq_not, Bool.not_not, and_true]
    exact Bool.eq_iff_iff.mpr (by simp [List.any_eq_true])
  have pred := (Represented.equal injectiveEncode i j).neg.both ((absEdge _ uv).both (absEdge _ vu))
  have fp : Represented q (fun d => [forbidden (es d.2.2) d.2.1 d.1]) := by
    apply pred.transport
    intro d
    by_cases a : d.2.1.2 = d.1.2 <;> by_cases b : (d.2.1.1, d.1.1) ∈ es d.2.2 <;>
      by_cases c : (d.1.1, d.2.1.1) ∈ es d.2.2 <;> simp [forbidden, a, b, c]
  have kept := (rs.snd V).filtered fp
  have idx : Represented q (fun d => E (d.2.1.2, d.1.2)) := i.packed j
  apply (rs.flatMap (kept.mapped idx)).transport
  intro x
  rw [← forbiddenRows]
  simp only [frames, List.map_flatMap, List.flatMap_assoc]

/-- An all-input polynomial-time program computes the original clique circuit on canonically
encoded graphs, including empty and malformed-endpoint graphs. -/
theorem represented_graphCircuit :
    Represented (bitEncode (α := ℕ × List (ℕ × ℕ))) (fun g =>
      let vs := vertices g.1 g.2
      bitEncode (vs.length, exclusionCircuit vs.length (forbiddenPairs vs g.2))) := by
  let es := bitEncode (α := List (ℕ × ℕ))
  have n : Represented (pair N es) (fun g => N g.1) := (Represented.input N).fst es
  have edges : Represented (pair N es) (fun g => frames E g.2) :=
    ((Represented.input es).snd N).transport (by intro g; exact (frames_encode g.2).symm)
  have vs := represented_vertices n edges
  exact represented_exclusionCircuit vs.count (represented_forbiddenPairs vs edges)

/-- The full reduction, including normalization of noncanonical natural numbers and rejection
of malformed graph encodings, is polynomial-time on ATLAS's canonical TM2 model. -/
theorem reduce_isPolyTime : IsPolyTime reduce := by
  let codec := CodecMachine.nat.prod (CodecMachine.nat.prod CodecMachine.nat).list
  obtain ⟨run, hr, hg⟩ := represented_graphCircuit
  have h := polyIf codec.polyValid (codec.polyNormalize.comp hr)
    (polyConst (bitEncode ((0, []) : ℕ × List WCGate)))
  convert h using 1
  funext x
  rw [codec.valid_eq]
  cases hd : bitDecode (α := ℕ × List (ℕ × ℕ)) x with
  | none => simp [reduce, hd]
  | some g => simp [reduce, hd, codec.normalize_eq hd, hg]

/-- Parameterized Clique belongs to W[1] under the given FPT many-one reductions. -/
theorem clique_mem_wLevel : CliqueParam ∈ WLevel 1 :=
  clique_mem_wLevel_of_isPolyTime reduce_isPolyTime

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CliqueMembership

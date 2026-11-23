/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-
# Basic computational-complexity definitions
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.Computable

@[expose] public section

namespace MetaMathlibExt

/-! A bitstring-specialized encoding API and basic definitions of `P`, `NP`,
and `coNP`.

This file adapts selected definitions from the following Apache-2.0 sources at
commit `62f56e8e4dab933a720f649721875c478b0ecf1c`:

* [`FormalConjecturesForMathlib/Computability/BitstringEncoding.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Computability/BitstringEncoding.lean)
* [`FormalConjecturesForMathlib/Computability/Complexity.lean`](https://github.com/google-deepmind/formal-conjectures/blob/62f56e8e4dab933a720f649721875c478b0ecf1c/FormalConjecturesForMathlib/Computability/Complexity.lean)

Local changes combine the selected APIs into one module, place them under
`MetaMathlibExt`, provide self-delimiting `Bool`, product, and list encodings,
and omit unrelated source instances and lemmas.
-/

open Computability

/-- **Bitstring encodings.** A canonical bitstring encoding of a type $\alpha$ consists of an
encoding map from $\alpha$ to finite lists of booleans and a partial decoding map from finite
lists of booleans to $\alpha$, such that decoding the encoding of any $a \in \alpha$ succeeds
and returns $a$.

Source: a class version of Mathlib's `Computability.Encoding` specialized to the alphabet
`Bool`, inlined from FormalConjectures (absent from Mathlib). -/
class BitstringEncoding α extends Computability.Encoding α Bool

namespace BitstringEncoding

variable {α β : Type*}

/-- **Encoding function of a bitstring encoding.** For a type $\alpha$ with a canonical bitstring
encoding, the bitstring encoding of $a \in \alpha$ is the finite list of booleans that this
encoding assigns to $a$. -/
def bitEncode [BitstringEncoding α] (a : α) : List Bool := toEncoding.encode a

/-- **Decoding function of a bitstring encoding.** For a type $\alpha$ with a canonical bitstring
encoding, bitstring decoding is the decoding function of that encoding: it sends each finite list
of booleans either to an element of $\alpha$ or to failure. -/
def bitDecode [BitstringEncoding α] (l : List Bool) : Option α := toEncoding.decode l

/-- **Decoding inverts bitstring encoding.** Let $\alpha$ be a type with a canonical bitstring
encoding. For every $a \in \alpha$, decoding the bitstring encoding of $a$ succeeds and returns
$a$. -/
@[simp]
theorem bitDecode_bitEncode [BitstringEncoding α] (a : α) :
    bitDecode (bitEncode a) = some a :=
  toEncoding.decode_encode a

/-- **Self-delimiting form of a bitstring.** The self-delimiting form of a bitstring
$(b_1, \dots, b_n)$ is $(\mathrm{true}, b_1, \dots, \mathrm{true}, b_n, \mathrm{false})$: each
bit is preceded by $\mathrm{true}$ and the block is terminated by $\mathrm{false}$. In
particular the empty bitstring becomes $(\mathrm{false})$. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- **Parsing one self-delimiting block.** Write booleans as bits, with true as $1$ and false as
$0$. Reading a list of bits from the front, a $0$ ends the block, and a $1$ followed by a bit $b$
contributes $b$ to the payload. The result is the payload together with the rest of the list
after the terminating $0$. Parsing fails if the list runs out before a terminating $0$ is read. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem length_delimit (l : List Bool) :
    (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; omega

/-- **Bounded parsing of self-delimiting blocks.** Given a bound $n$ and a list of booleans $s$,
the parse returns the empty list of payloads if $s$ is empty. If $s$ is nonempty and $n = 0$ it
fails. If $s$ is nonempty and $n = m + 1$, it parses one self-delimiting block from the front of
$s$, then parses the remaining list with bound $m$, and returns the first payload followed by the
payloads of the rest. It fails if either step fails. So the parse succeeds exactly when $s$ is
the concatenation of at most $n$ self-delimiting blocks, and it returns their payloads in order. -/
def undelimitBlocksAux : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input =>
    (undelimit input).bind fun p => (undelimitBlocksAux fuel p.2).map (p.1 :: ·)

/-- **Parsing a list of booleans into self-delimiting blocks.** Given a list of booleans $s$, this
repeatedly parses one self-delimiting block from the front of $s$ until $s$ is used up, allowing
at most as many blocks as the length of $s$, and returns the list of payloads in order. It fails
if some block fails to parse. The bound never binds, since every block uses at least one bit.
So the parse succeeds exactly when $s$ is a concatenation of self-delimiting blocks. -/
def undelimitBlocks (input : List Bool) : Option (List (List Bool)) :=
  undelimitBlocksAux input.length input

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      length_delimit]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) (fuel : ℕ)
    (hfuel : l.length ≤ fuel) :
    undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons b t ih =>
    rw [List.length_cons] at hfuel
    cases fuel <;> cases b <;> grind [delimit, undelimitBlocksAux, undelimit_delimit]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp]
theorem mapM_bitDecode_map_bitEncode [BitstringEncoding α] (l : List α) :
    (l.map bitEncode).mapM bitDecode = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- A pair is encoded as a self-delimiting block for the first component
followed by the encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (bitEncode p.1) ++ bitEncode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match bitDecode block, bitDecode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its
elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map bitEncode).map delimit).flatten
  decode input := (undelimitBlocks input).bind (·.mapM bitDecode)
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map bitEncode)]
    exact mapM_bitDecode_map_bitEncode l

end BitstringEncoding

namespace ComplexityTheory

/-- **Decision problems.** A decision problem is a function from finite lists of booleans
(bitstrings) to booleans.

Source: inlined from FormalConjectures (absent from Mathlib). -/
abbrev DecisionProblem := List Bool → Bool

/-- **Complexity classes.** A complexity class is a set of decision problems.

Source: inlined from FormalConjectures (absent from Mathlib). -/
abbrev DecisionComplexityClass := Set DecisionProblem

/-- **Polynomial-time computability under given encodings.** Let $e_\alpha$ encode $\alpha$ as
words over an alphabet $\Gamma_\alpha$ and $e_\beta$ encode $\beta$ as words over $\Gamma_\beta$. A
function $f : \alpha \to \beta$ is polynomial-time computable with respect to $e_\alpha$ and
$e_\beta$ when there are a multi-stack Turing machine with finitely many stacks, function labels
and internal states and a finite input stack alphabet, identifications of its input and output
stack alphabets with $\Gamma_\alpha$ and $\Gamma_\beta$, and a polynomial $p$ with natural-number
coefficients, such that for every $a \in \alpha$ the machine, started at its main function in its
initial state with $e_\alpha(a)$ on its input stack and every other stack empty, halts within
$p(n)$ steps, where $n$ is the length of $e_\alpha(a)$, with $e_\beta(f(a))$ on its output stack,
every other stack empty and its internal state equal to its initial state.

Source: inlined from FormalConjectures (absent from Mathlib). -/
def IsPolyTimeWithEncoding {α β Γα Γβ : Type} (ea : Encoding α Γα)
    (eb : Encoding β Γβ) (f : α → β) :=
  Nonempty (Turing.TM2ComputableInPolyTime ea.encode eb.encode f)

/-- **Polynomial-time computable functions.** Let $\alpha$ and $\beta$ be types with canonical
bitstring encodings. A function $f : \alpha \to \beta$ is polynomial-time computable when it is
polynomial-time computable with respect to the canonical bitstring encodings of $\alpha$ and
$\beta$.

Source: inlined from FormalConjectures (absent from Mathlib). -/
def IsPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) : Prop :=
  IsPolyTimeWithEncoding (BitstringEncoding.toEncoding (α := α))
    (BitstringEncoding.toEncoding (α := β)) f

/-- **The complexity class P.** P is the set of decision problems (functions from lists of
booleans to booleans) that are computable in polynomial time by a deterministic multi-stack
Turing machine, with respect to the canonical bitstring encodings of inputs and outputs.

Source: adapted from FormalConjectures,
FormalConjecturesForMathlib/Computability/Complexity.lean (absent from Mathlib). -/
def P : DecisionComplexityClass :=
  { L | IsPolyTime L }

/-- **The complexity class NP.** NP is the set of decision problems $L$ (functions from lists of
booleans to booleans) for which there exist a polynomial $p$ with natural-number coefficients and
a polynomial-time computable function $R$ from pairs of lists of booleans to booleans such that,
for every list of booleans $x$, $L(x)$ is true if and only if there is a list of booleans $w$
whose length is at most $p$ evaluated at the length of $x$ and for which $R(x, w)$ is true.

Polynomial time is measured with respect to the canonical bitstring encodings.

Source: adapted from FormalConjectures,
FormalConjecturesForMathlib/Computability/Complexity.lean (absent from Mathlib). -/
def NP : DecisionComplexityClass :=
  { L | ∃ (p : Polynomial ℕ), ∃ R : (List Bool × List Bool) → Bool,
      IsPolyTime R ∧
      ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ R (x, w) }

/-- **The class coNP.** coNP is the set of decision problems $L$ whose complement, the decision
problem that accepts exactly the bitstrings that $L$ rejects, belongs to NP.

Source: inlined from FormalConjectures (absent from Mathlib). -/
def coNP : DecisionComplexityClass :=
  { L | Lᶜ ∈ NP }

end ComplexityTheory

end MetaMathlibExt

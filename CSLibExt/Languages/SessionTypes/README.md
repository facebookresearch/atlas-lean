# Finite session typing: source correspondence and limits

## Primary reference and version examined

Kohei Honda, Vasco T. Vasconcelos and Makoto Kubo,
*Language primitives and type discipline for structured communication-based
programming*, ESOP 1998, Lecture Notes in Computer Science 1381, pp. 122–138.
[Publisher DOI](https://doi.org/10.1007/BFb0053567).

The rule correspondence below was checked against the authors' nineteen-page
manuscript [available here][hvk-manuscript], particularly §2.3, pp. 5–6,
Definitions 5.1–5.3 and Figure 1, pp. 11–13, and Theorem 5.4, p. 14.
These are manuscript page numbers, not the Springer chapter pagination.
The figure itself was read from the PDF, not reconstructed from search snippets.

This development is an original, restricted and sort-erased model grounded in
that binary-session discipline. It is **not a formalization of the entire paper**,
nor is equivalence between its typing derivations and `HasType` proved.

## Protocol constructors and duality

Definition 5.1 uses `↑[S̃]; α` for sending data and `↓[S̃]; α` for receiving
data, followed by protocol `α`; `1` denotes inaction. `SessionType.send s`,
`SessionType.recv s` and `SessionType.end` retain just that sequencing shape.
The payload-sort vector is erased and arity is fixed to one passive name.
The manuscript's co-type swaps sending and receiving while fixing `1`.
`SessionType.dual` implements this finite data-action part of co-typing.

The source also includes selection/branching, recursive types and separate
channel-passing types. None is represented here. In particular, `end` is not
the source's `⊥`, which records a channel already composed with its peer and
has no co-type. There is no session subtyping relation in this development.

## Every typing rule

The source judgment is `Θ; Γ ⊢ P ▷ Δ`: process-variable assumptions `Θ`,
a finite partial sorting `Γ` for shared names/data variables, and a finite
partial channel typing `Δ`. Our judgment is `HasType n Γ p`. Our `Γ` is the
**linear channel bookkeeping**, not the source's sorting with the same letter.
`n` records only the number of in-scope input variables. Scope checking is not
payload sort checking. All three constructors have the following correspondence:

- **`HasType.nil` and Figure 1 `[Inact]`:** the source types inaction when
  the range of `Δ` contains only `1` and `⊥`. Here every entry of the total
  context must be `end`, corresponding to the completed `1` case alone.
  There is no `⊥` case, composition accounting or permission to discard an
  outstanding send/receive obligation.
- **`HasType.out` and `[Send]`:** the source checks `Γ ⊢ ẽ ▷ S̃` and types
  the continuation with `k : α`, then assigns `k : ↑[S̃]; α` to the prefix.
  Here `Γ a = send s` is the head obligation, and `advance Γ a s` types the
  continuation while preserving every other channel entry. The subject is
  restricted to `Name.const a`; the payload is an already available `Name`
  with `b.ClosedAt n`. There is no expression evaluation or sort judgment.
  This is a monadic, scope-checked, sort-erased data-send projection of `[Send]`,
  **not** the delegation rule `[Thr]`.
- **`HasType.inp` and `[Rcv]`:** the source extends its sorting with received
  variables of the prescribed sorts, types the continuation with `k : α`,
  and assigns `k : ↓[S̃]; α` to the prefix. Here the channel advances to `s`
  and the continuation is checked at depth `n + 1`, using the existing π
  de Bruijn binder. The received variable is unrestricted passive data, not
  a newly owned linear endpoint. It cannot become a session subject through
  this rule. No capability is inserted into the linear context.

These rules have no parallel, restriction, initiation, recursive-process or
choice constructor. The source's `[Acc]`, `[Req]`, `[Br]`, `[Sel]`, `[Thr]`,
`[Cat]`, `[Conc]`, `[If]`, `[NRes]`, `[CRes]`, `[Var]` and `[Def]` are omitted,
not silently supplied by an assumption.

## Representation differences

1. **Subjects and payloads:** the source distinguishes session channels from
   shared names and data variables. This model uses existing π names for both
   positions, but only constant subjects. A payload may have the same printed
   name as a session channel, or be forwarded repeatedly; this does not transfer
   or duplicate its linear capability. Bound-name subjects, dynamic topology
   through delegation, and typed shared services are absent.
2. **Contexts:** `Context := Nat → SessionType` is a total per-thread function
   with one obligation per constant channel. `HasType.finite_support` proves
   that every derivable context is `end` above some bound. This finiteness result
   does not make the representation literally the source's finite partial map:
   absence and completion are conflated, and the source's `⊥` is missing.
   `advance` replaces exactly one entry. There is no linear context splitting.
3. **Peers:** `BinaryTyped Γ (p,q)` gives the second sequential thread the
   pointwise dual context on the same physical names. The source's Definition
   5.2 and `[Conc]` instead compose compatible partial channel typings and
   mark common channels `⊥`. The pair predicate does not implement that general
   composition algebra and does not type arbitrary π parallel compositions.
4. **Reduction:** §2.3 `[Com]` synchronizes data guards and substitutes received
   values after expression evaluation. `CommStep` uses the corresponding
   monadic substitution shape on existing π guards, with the payload already
   a name value. Its representation into `PiCalculus.Step` is proved in both
   orientations. This is not the paper's translation into asynchronous π,
   and preservation is for direct pair communication, not every π reduction
   modulo structural congruence.

## Exact theorem scope

Theorem 5.4 of the source concerns structural invariance, subject reduction
and lack of interaction errors. It does **not** supply an unrestricted
well-typed-implies-deadlock-free theorem. This development does not port that
entire theorem: `CommStep.preservation` exposes dual residual contexts after
one direct communication.

`progress` additionally assumes `SingleChannel Γ a`, so the two sequential
threads own at most the same one active session. That is a project-authored
structural hypothesis, not a premise attributed to the source. The typed
cyclic-wait consumer shows why local duality alone is insufficient, including
absence of every π reduction via the shared unguarded-output invariant.
`finite_completion` constructs a finite path for isolated finite sessions;
it says neither that arbitrary π processes normalize nor that recursive
sessions terminate. All source rules omitted above remain outside this result.

[hvk-manuscript]: https://filipendule.github.io/mgs/honda.vasconcelos.kubo.pdf

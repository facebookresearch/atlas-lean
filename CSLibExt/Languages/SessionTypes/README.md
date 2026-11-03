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

This development is a project-authored, restricted and sort-erased model
of that binary-session discipline. It is **not a formalization of the entire
paper**, nor is equivalence between its typing derivations and `HasType` proved.

## Lean development provenance

An earlier revision of `CSLibExt/Languages/SessionTypes/Basic.lean`, development
revision `a578d21dd840e286f88b1799fee9403c902b6f24`, is preserved verbatim in the
[source snapshot][lean-source], with its origin and exact bytes recorded in the
[provenance manifest][lean-manifest]. It is an earlier version of this same
project-authored module, not an unrelated external formalization. The current
module carries forward the following Lean declarations from that version.

The line numbers below refer to the 164-line snapshot. "Unchanged" means the
statement and implementation/proof, not the surrounding explanatory comments.
"Added" means absent from this snapshot, not a claim of independent novelty.

| Snapshot declaration and lines | Current declaration | Relationship |
| --- | --- | --- |
| `SessionType`, 30–34 | `SessionType` | Reused unchanged, including `end`/`send`/`recv`. |
| `SessionType.dual`, 37–40; `dual_dual`, 43–45 | Same declarations | Reused unchanged. |
| `SessionType.length`, 48–51; `length_dual`, 54–56 | Same declarations | Reused unchanged. |
| `Context`, 59; `advance`, 62–63 | Same declarations | Reused unchanged. |
| `dualContext`, 66; `dualContext_advance`, 69–73 | Same declarations | Reused unchanged. |
| `NameScoped`, 76–78; `NameScoped.lift`, 81–87; `NameScoped.subst`, 90–103 | Imported π `Name.ClosedAt` and transport | Removed locally; canonical scoping replaces the same scoped-name concept. The provenance manifest records the π adaptations. |
| `HasType`, 108; `HasType.nil`, 109 | Same judgment shape and `nil` rule | Reused unchanged; the `out` adaptation is recorded below. |
| `HasType.out`, 110–112 | `HasType.out` | Adapted: `NameScoped n b` becomes canonical `b.ClosedAt n`; channel advancement is unchanged. |
| `HasType.inp`, 113–115 | `HasType.inp` | Reused unchanged. |
| `HasType.substProc`, 119–137 | `HasType.substProc` | Adapted scoping hypothesis and imported name-transport API; proof text unchanged. |
| `HasType.subst`, 140–143 | `HasType.subst` | Adapted `NameScoped 0 b` hypothesis to `b.ClosedAt 0`; proof unchanged. |
| `HasType.finite_support`, 147–162 | `HasType.finite_support` | Reused unchanged. |
| No declaration in the snapshot | `HasType.closedAt` | Added later: typed threads satisfy canonical π process scoping. |

The import at snapshot line 11 changes from π `Basic` to π `Scoping`. This
accounts for the canonical scope predicates and transport used by the adapted
rules; it does not change their finite/passive-name restrictions. The separate
`Communication` and `Progress` modules are not contained in this `Basic`
snapshot, so the table does not attribute their declarations to it.

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
[lean-source]: ../../../docs/provenance/pi-scoping/finite-session-basic.lean.txt
[lean-manifest]: ../../../docs/provenance/pi-scoping/manifest.json

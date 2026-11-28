# Determinism constancy makes footprints the smallest safe states

If adding resource to a safe state frames a local function's outcomes exactly, rather than merely bounding them, its footprints are exactly its smallest safe states. The property is preserved by sequential composition, choice and iteration, so it lifts from primitive commands to every program.

Let $(\Sigma, \bullet, u)$ be a separation algebra. Extend $f : \Sigma \to P(\Sigma)^\top$ to sets by $f(A) = \bigsqcup_{\sigma \in A} f(\sigma)$, so that $f(\emptyset) = \emptyset$. A local function $f$ has *determinism constancy* if, for every $\sigma$ with $f(\sigma) \neq \top$ and every $\sigma' \in \Sigma$,

$$f(\{\sigma'\} \ast \{\sigma\}) = \{\sigma'\} \ast f(\{\sigma\}),$$

including when $\sigma' \bullet \sigma$ is undefined, where the left side is $\emptyset$ and the condition requires $\{\sigma'\} \ast f(\sigma) = \emptyset$.

1. If a local function has determinism constancy, its [footprints](footprints-of-local-functions.md) are exactly its smallest safe states.
2. For the commands $C ::= c \mid \mathbf{skip} \mid C ; C \mid C + C \mid C^\ast$ of [abstract separation logic](../abstract-separation-logic/abstract-separation-logic-rules.md), with their local-action semantics, if every primitive command denotes a function with determinism constancy, then so does every command, and the footprints of every command are its smallest safe states.

## Depends on

- [Footprints of local functions](footprints-of-local-functions.md)
- [Abstract separation logic](../abstract-separation-logic/abstract-separation-logic-rules.md)

## Proof depends on

- [Footprints of local functions](footprints-of-local-functions.md)
- [Abstract separation logic](../abstract-separation-logic/abstract-separation-logic-rules.md)

## Expansion

Part 1: smallest safe states are footprints. Every other safe state $\tau$ has a safe strict substate $\sigma$, and writing $\tau = \sigma' \bullet \sigma$, determinism constancy gives $f(\tau) = \{\sigma'\} \ast f(\sigma) \sqsupseteq L_f(\tau)$, so $\tau$ is not a footprint; unsafe states never are. Part 2 is an induction on commands: for sequential composition push the frame through $f$ and then through $g$ on each intermediate outcome, which is safe for $g$, and use that $\{\sigma'\} \ast (\cdot)$ distributes over unions; choice and iteration are similar. Example from the source: in the stack-and-heap model, allocation, mutation and lookup have determinism constancy but disposal does not. In the model whose states are built from cells $l \mapsto v$, variables $x \mapsto v$ and at most one *free set* $F \subseteq L$ disjoint from the allocated locations, where allocation and disposal require the free set, take the new address from it or return the old address to it, and fault otherwise, all four commands have determinism constancy; so in that model the footprints of every program are its smallest safe states, and the allocate-then-deallocate command has the states $x \mapsto v \bullet F$ as its only footprints. Disposal in the stack-and-heap model fails because framing a cell at the disposed address makes the input undefined, giving $\emptyset$, while framing the output is defined; with a free set, allocation draws from $F$, so its outcomes do not depend on cells framed in.

## Sources

- M. Raza and P. Gardner, "Footprints in local reasoning", *Logical Methods in Computer Science* 5(2:4), 2009, <https://doi.org/10.2168/LMCS-5(2:4)2009>, arXiv:0903.1032v2 <https://arxiv.org/abs/0903.1032v2>, Section 6.1, Example 6.1 and Lemma 6.2; Section 6.2; Section 6.3, Definition 6.3, Lemma 6.4, Theorem 6.5 and Proposition 6.6 with their proofs (numbers from arXiv:0903.1032v2).

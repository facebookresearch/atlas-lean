# Asynchronous subtyping of binary session types is undecidable

No algorithm decides, given two binary session types $T$ and $S$, whether $T$ is an asynchronous subtype of $S$; this settles the decidability of the subtyping relation of Mostrous and Yoshida for binary session types.

**Theorem.** The following problem is undecidable. Input: two binary session types $T$ and $S$ (selection, branching, recursion and $\mathbf{end}$ over a set of labels). Question: does $T \le S$ hold, where $\le$ is [asynchronous subtyping](asynchronous-subtyping-of-binary-session-types.md)? Instances are finite type terms, each using finitely many labels; the types produced by the reduction are closed, use finitely many labels and have input-guarded recursion, so the problem stays undecidable on those inputs.

## Depends on

- [Asynchronous subtyping of binary session types](asynchronous-subtyping-of-binary-session-types.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Asynchronous single-choice subtyping is undecidable](asynchronous-single-choice-subtyping-undecidable.md)

## Expansion

The single-choice relation $\le_{\mathsf{sc}}$ is $\le$ restricted to the pairs in $(T^{\mathsf{out}} \times T^{\mathsf{in}}) \cap (\mathit{NOINF} \times \mathit{NOINF})$, a decidable set of pairs. If $\le$ were decidable, so would be its intersection with a decidable set, contradicting the undecidability of $\le_{\mathsf{sc}}$. The same queue-machine encoding carries over to standard binary session types with message payloads (same source, Corollary 4.2) and to multiparty asynchronous subtyping (Corollary 4.4). Lange and Yoshida obtained an undecidability result for asynchronous subtyping independently.

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "Undecidability of asynchronous session subtyping", *Information and Computation* 256, 300–320, 2017, <https://doi.org/10.1016/j.ic.2017.07.010>; read as arXiv:1611.05026v3, <https://arxiv.org/abs/1611.05026v3>: Corollary 4.1 and its proof, in Section 4 of that version.

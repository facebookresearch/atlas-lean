# Asynchronous single-choice subtyping is undecidable

Asynchronous subtyping is undecidable already when the subtype has only single-label outputs, the supertype only single-label inputs, and both have input-guarded recursion; acceptance of queue machines reduces to its complement.

Let $T^{\mathsf{out}}$ be the session types whose selections all have one label ($\oplus\{l : T\}$, branchings unrestricted), $T^{\mathsf{in}}$ those whose branchings all have one label ($\&\{l : T\}$, selections unrestricted), and $\mathit{NOINF}$ those in which, for every subterm $\mu \mathbf{t}.R$, every occurrence of $\mathbf{t}$ in $R$ lies inside a branching $\&\{l_i : S_i\}_{i \in I}$ of $R$. The asynchronous single-choice relation is

$$
\le_{\mathsf{sc}} \;=\; \le \cap\, (T^{\mathsf{out}} \times T^{\mathsf{in}}) \cap (\mathit{NOINF} \times \mathit{NOINF}),
$$

where $\le$ is [asynchronous subtyping](asynchronous-subtyping-of-binary-session-types.md).

**Theorem.** The following problem is undecidable. Input: two session types $T$ and $S$. Question: does $T \le_{\mathsf{sc}} S$ hold? Instances are finite type terms over finitely many labels; the source shows that a queue machine $M$ does not accept an input $x$ exactly when $T \le_{\mathsf{sc}} S$ for two closed types computed from $M$ and $x$: $T$ encodes the control of $M$ from its start state, and $S$ encodes the initial queue content, $x$ followed by the end marker.

## Depends on

- [Asynchronous subtyping of binary session types](asynchronous-subtyping-of-binary-session-types.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the acceptance problem for queue machines, which are Turing-complete. A queue machine $M = (Q, \Sigma, \Gamma, \#, s, \delta)$ with input $x$ and initial queue symbol $\#$ is encoded by a type $T = [\![s]\!]^{\emptyset}$ for the finite control, which performs one input per dequeued symbol followed by outputs for the enqueued symbols, and a type $S = [\![x\#]\!]$ for the queue content. In the simulation game for $T \le S$, outputs of $T$ are matched by anticipating outputs nested under the inputs of $S$, so the queue grows exactly as in $M$. The source proves that $M$ accepts $x$ if and only if $T \not\le_{\mathsf{sc}} S$ (its Theorem 3.1); undecidability of acceptance gives the result (Corollary 3.1). The relation is not reflexive: $\&\{l_1 : \mathbf{end}, l_2 : \mathbf{end}\}$ is not single-choice related to itself.

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "Undecidability of asynchronous session subtyping", *Information and Computation* 256, 300–320, 2017, <https://doi.org/10.1016/j.ic.2017.07.010>; read as arXiv:1611.05026v3, <https://arxiv.org/abs/1611.05026v3>: Definitions 3.1–3.4 (single outputs, single inputs, input-guarded recursion, the single-choice relation), Theorem 3.1 and Corollary 3.1 of that version.

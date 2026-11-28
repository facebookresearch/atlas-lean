# Accuracy of randomized programs is undecidable

Whether a randomized program, such as a differential privacy mechanism, meets a given accuracy specification relative to the deterministic function it approximates is undecidable, both at a given input and at all inputs.

**Accuracy.** Let $P$ be a randomized program with inputs $\mathcal{U}$ and outputs $\mathcal{V}$, measured against a deterministic program $\det(P)$, with an input distance $d$ on $\mathcal{U}$ and, for each input $u$, an output distance $d'_u$ on $\mathcal{V}$. The *disagreement distance* of $P$ at $u$ is $\mathrm{dd}(P, u) = d(u, \mathcal{U} \setminus \det(P)^{-1}(\det(P)(u)))$, the distance from $u$ to the nearest input on which $\det(P)$ gives another output. Write $B(v, u, \gamma) = \{v' \in \mathcal{V} : d'_u(v, v') \leq \gamma\}$. For $\alpha, \gamma \geq 0$ and $\beta \in [0,1]$, $P$ is *$(\alpha, \beta, \gamma)$-accurate at $u$* if $\mathrm{dd}(P, u) > \alpha$ implies

$$
\Pr\big(P(u) \in B(\det(P)(u), u, \gamma)\big) \geq 1 - \beta .
$$

For a program $P_\epsilon$ depending on a privacy budget $\epsilon$ in an interval $I$, and an admissible region $\mathrm{reg}(\epsilon, u)$ of triples $(\alpha, \beta, \gamma)$:

- *Accuracy-at-an-input*: given $u$, is $P_\epsilon$ $(\alpha, \beta, \gamma)$-accurate at $u$ for all $\epsilon \in I$ and all $(\alpha, \beta, \gamma) \in \mathrm{reg}(\epsilon, u)$?
- *Accuracy-at-all-inputs*: does this hold for every input $u$?

**Theorem (Barthe, Chadha, Krogmeier, Sistla and Viswanathan).** Both Accuracy-at-an-input and Accuracy-at-all-inputs are undecidable for the general class of randomized programs (Theorem 8).

The proof in the appendix of the source uses only programs independent of $\epsilon$ with $\mathcal{U} = \mathcal{V} = \{0, 1\}$, both distances equal to $1$ between distinct points, and the single triple $(0, 0, 0)$. By contrast, the source identifies a non-trivial class of probabilistic programs for which accuracy is decidable, unconditionally or assuming Schanuel's conjecture (Section 6).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Given a two-counter machine $M$, build a program $P$ with input $\mathit{in} \in \{0,1\}$ that outputs $1$ at once on input $1$. On input $0$ it repeats: if the stored control state is final, output $1$ and stop; otherwise, with probability $1/2$ jump to the final state, and with probability $1/2$ simulate one step of $M$ on stored counters. Then on input $0$ the output is $0$ with probability $1$ iff $M$ does not halt from zero counters. With $\det(P)$ the identity on $\{0,1\}$, $P$ is $(0,0,0)$-accurate at input $0$ iff $M$ does not halt.

## Sources

- Gilles Barthe, Rohit Chadha, Paul Krogmeier, A. Prasad Sistla and Mahesh Viswanathan, "Deciding accuracy of differential privacy schemes", *Proceedings of the ACM on Programming Languages* 5(POPL), 30 pages, 2021, doi:10.1145/3434289; read as arXiv:2011.06404v1, <https://arxiv.org/abs/2011.06404v1>: Definitions 1 and 2, the problem definitions of Section 4, Theorem 8 and its proof in the appendix of arXiv:2011.06404v1.

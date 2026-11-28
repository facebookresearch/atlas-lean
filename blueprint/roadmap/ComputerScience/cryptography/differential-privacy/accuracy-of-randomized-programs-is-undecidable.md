# Accuracy of randomized programs is undecidable

Whether a randomized program, such as a differential privacy mechanism, meets a given accuracy specification relative to the deterministic function it approximates is undecidable, both at a given input and at all inputs.

**Accuracy.** Let $P$ be a randomized program with inputs $\mathcal{U}$ and outputs $\mathcal{V}$, measured against a deterministic program $\det(P)$, with an input distance $d$ on $\mathcal{U}$ and, for each input $u$, an output distance $d'_u$ on $\mathcal{V}$. The *disagreement distance* of $P$ at $u$ is $\mathrm{dd}(P, u) = d(u, \mathcal{U} \setminus \det(P)^{-1}(\det(P)(u)))$, the distance from $u$ to the nearest input on which $\det(P)$ gives another output. Write $B(v, u, \gamma) = \{v' \in \mathcal{V} : d'_u(v, v') \leq \gamma\}$. For $\alpha, \gamma \geq 0$ and $\beta \in [0,1]$, $P$ is *$(\alpha, \beta, \gamma)$-accurate at $u$* if $\mathrm{dd}(P, u) > \alpha$ implies

$$
\Pr\big(P(u) \in B(\det(P)(u), u, \gamma)\big) \geq 1 - \beta .
$$

For a program $P_\epsilon$ depending on a privacy budget $\epsilon$ in an interval $I$, and an admissible region $\mathrm{reg}(\epsilon, u)$ of triples $(\alpha, \beta, \gamma)$:

- *Accuracy-at-an-input*: given $u$, is $P_\epsilon$ $(\alpha, \beta, \gamma)$-accurate at $u$ for all $\epsilon \in I$ and all $(\alpha, \beta, \gamma) \in \mathrm{reg}(\epsilon, u)$?
- *Accuracy-at-all-inputs*: does this hold for every input $u$?

**Theorem (Barthe, Chadha, Krogmeier, Sistla and Viswanathan).** Both Accuracy-at-an-input and Accuracy-at-all-inputs are undecidable for the general class of randomized programs (Theorem 8). In the finite-input form given by the corrected proof (`## Expansion`), instances are [fully probabilistic programs](../../program-logics-and-verification/expected-run-time-calculus/probabilistic-programs-with-a-run-time-model.md) with values in $\mathbb N$ and fair coin flips as distribution expressions, given by their text, with inputs and outputs in $\{0, 1\}$, $\det(P)$ the identity on $\{0, 1\}$, both distances discrete ($d(0, 1) = d'_u(0, 1) = 1$), $\mathrm{reg} = \{(0, 0, 0)\}$ and no dependence on $\epsilon$. For these:

1. it is undecidable, given $P$, whether $P$ is $(0, 0, 0)$-accurate at input $0$;
2. it is undecidable, given $P$, whether $P$ is $(0, 0, 0)$-accurate at every input. The programs of the reduction output $1$ with probability $1$ on input $1$, so they are accurate at $1$ and the two questions agree on them; on the whole class the two properties differ (a program that outputs $0$ on both inputs is accurate at $0$ but not at $1$).

The source does not fix a syntax for the general class of randomized programs, and its Theorem 8 is stated for that class; $I$ is an interval with rational end-points. By contrast, the source identifies a non-trivial class of probabilistic programs for which accuracy is decidable, unconditionally or assuming Schanuel's conjecture (Section 6).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Probabilistic programs with a run-time model](../../program-logics-and-verification/expected-run-time-calculus/probabilistic-programs-with-a-run-time-model.md)
- [Operational Markov decision process of a probabilistic program](../../program-logics-and-verification/expected-run-time-calculus/operational-markov-decision-process-of-a-probabilistic-program.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Given a two-counter machine $M$, build a program $P$ with input $\mathit{in} \in \{0,1\}$ that outputs $1$ at once on input $1$. On input $0$ it repeats: if the stored control state is final, output $1$ and stop; otherwise, with probability $1/2$ output $0$ and stop, and with probability $1/2$ simulate one step of $M$ on stored counters. If $M$ halts from zero counters after $k$ steps, the output on input $0$ is $1$ with probability $2^{-k} > 0$; if it never halts, the output is $0$ with probability $1$. With $\det(P)$ the identity on $\{0,1\}$, the disagreement distance at $0$ is $1 > 0$, so $P$ is $(0,0,0)$-accurate at input $0$ iff $M$ does not halt. The appendix of the source (proof of Theorem 8) lets the coin jump to the final state instead, which makes the output $1$ with probability $1$ on every machine; the stop-with-output-$0$ step is the correction that makes the reduction work.

A good expansion adds and links a page defining the output distribution $\Pr(P(u) = v)$ of a fully probabilistic program from its operational Markov decision process (linked above), the quantity the accuracy condition is about.

## Sources

- Gilles Barthe, Rohit Chadha, Paul Krogmeier, A. Prasad Sistla and Mahesh Viswanathan, "Deciding accuracy of differential privacy schemes", *Proceedings of the ACM on Programming Languages* 5(POPL), 30 pages, 2021, doi:10.1145/3434289; read as arXiv:2011.06404v1, <https://arxiv.org/abs/2011.06404v1>: Definitions 1 and 2, the problem definitions of Section 4, Theorem 8 and its proof in the appendix of arXiv:2011.06404v1.

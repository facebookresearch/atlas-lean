# Almost-sure termination of order-2 probabilistic recursion schemes is undecidable

Whether a probabilistic higher-order recursion scheme of order $2$ terminates with probability $1$ is undecidable; the set of almost surely terminating order-2 schemes is even $\Pi^0_1$-hard. At order $1$ the problem is decidable, as the paper notes via recursive Markov chains, so order $2$ is the threshold.

**Theorem (Kobayashi, Dal Lago and Grellois).**

1. The set $\{ \mathcal{G} : \mathcal{G} \text{ is an order-2 pHORS with } \mathcal{P}(\mathcal{G}) = 1 \}$ is $\Pi^0_1$-hard; in particular almost-sure termination of order-2 pHORS is undecidable.
2. For every rational $r \in (0, 1]$, the sets $\{ \mathcal{G} \text{ of order } 2 : \mathcal{P}(\mathcal{G}) \ge r \}$ and $\{ \mathcal{G} \text{ of order } 2 : \mathcal{P}(\mathcal{G}) = r \}$ are $\Pi^0_1$-hard, so deciding $\mathcal{P}(\mathcal{G}) \ge r$ or $\mathcal{P}(\mathcal{G}) = r$ is undecidable.

The scheme is part of the input; the order is fixed at $2$. For $r = 0$ both sets are decidable, and for every rational $r \in [0, 1]$ the set of schemes with $\mathcal{P}(\mathcal{G}) > r$ is recursively enumerable, because termination probabilities can be approximated from below.

## Depends on

- [Probabilistic higher-order recursion schemes](probabilistic-higher-order-recursion-schemes.md)
- [The arithmetical class Πₙ](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

From Hilbert's tenth problem: whether $P(\vec{x}) < Q(\vec{x})$ for some $\vec{x} \in \mathbb{N}^k$, for polynomials $P, Q$ with non-negative integer coefficients, is $\Sigma^0_1$-complete (write $D^2 - 1 = P - Q$ for an integer polynomial $D$). From $P$ and $Q$ the proof builds an order-2 scheme that enumerates the tuples $\vec{x}$ and, using probabilistic choices to compare $P(\vec{x})$ with $Q(\vec{x})$, fails to terminate almost surely exactly when $P(\vec{x}) < Q(\vec{x})$ for some $\vec{x}$; an order-3 construction is given first and then lowered to order $2$. Part 2 follows by adding a start rule $S' = S \oplus_r \Omega$, which multiplies the termination probability by $r$.

## Sources

- Naoki Kobayashi, Ugo Dal Lago and Charles Grellois, "On the Termination Problem for Probabilistic Higher-Order Recursive Programs", Logical Methods in Computer Science 16(4), Article 2, 2020, <https://doi.org/10.23638/LMCS-16(4:2)2020>; Theorem 3.2 (part 1), Theorem 3.3 (part 2), Lemma 3.1 (the Diophantine form) and Remark 3.4 (the r.e. and decidable cases) of arXiv:1811.02133v5, <https://arxiv.org/abs/1811.02133v5>.

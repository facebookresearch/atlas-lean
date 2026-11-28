# Termination of two-piece affine integer loops is undecidable

Termination is undecidable already for integer loops with a linear guard and an update that applies one of two integer matrices depending on the sign of a single variable, both from all initial states and from a given set of initial states.

**Theorem.** The termination problem, with and without an initial set of states (a polyhedral set given by rational linear inequalities), is undecidable for loops of the form

$$
\mathbf{while}\ (B\vec x \ge \vec b)\ \mathbf{do}\ \vec x := \begin{cases} A_0 \vec x & \text{if } x_i \le 0, \\ A_1 \vec x & \text{if } x_i > 0, \end{cases}
$$

where the state $\vec x$ ranges over $\mathbb Z^n$, $A_0, A_1 \in \mathbb Z^{n \times n}$, $B \in \mathbb Z^{p \times n}$ and $\vec b \in \mathbb Z^p$ for some $p > 0$, and $x_i$ is one of the variables. Each such loop is a deterministic [multipath linear-constraint loop](linear-constraint-loops.md) with two paths.

The source credits this result (Theorem 3.8 there) to Ben-Amram, Genaim and Masud (ACM TOPLAS 2012), whose proof reduces from $2$-counter programs.

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The result is due to Ben-Amram, Genaim and Masud, who prove it by a reduction from two-counter programs, whose termination is undecidable; the survey states the result and the source of the reduction without reproducing it. The same survey records related results: termination of deterministic loops $\mathbf{while}\ (x_1 + x_2 > 0)\ \mathbf{do}\ (x_1, x_2) := f(x_1, x_2)$ with $f$ piecewise affine is undecidable over $\mathbb Q$ and $\mathbb R$ (Blondel and coauthors) and over $\mathbb Z$ (Ben-Amram).

## Sources

- Amir M. Ben-Amram, Samir Genaim, Joël Ouaknine and James Worrell, "Termination Analysis of Linear-Constraint Programs", *Foundations and Trends in Programming Languages* 10(1–2), 2026, pp. 1–145, <https://doi.org/10.1108/FTPGL-07-2025-0071>; read as arXiv:2509.06752v3, <https://arxiv.org/abs/2509.06752v3>: Theorem 3.8 in Section 3.3 ("Termination of Multi-path Linear-Constraint Loops"), in the numbering of that version.

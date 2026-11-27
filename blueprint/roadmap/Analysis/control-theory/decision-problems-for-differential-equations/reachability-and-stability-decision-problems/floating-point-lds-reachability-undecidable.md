# Point-to-point reachability for linear dynamical systems under floating-point rounding is undecidable

When a rational matrix is applied repeatedly to a vector and every coordinate is rounded to a floating-point number after each step, no algorithm decides whether a given target vector appears in the rounded orbit, although without rounding point-to-point reachability is decidable in polynomial time.

**Setting.** A $d$-dimensional linear dynamical system $(M, x)$ consists of $M \in \mathbb Q^{d \times d}$ and $x \in \mathbb Q^d$. For a precision $p \in \mathbb N$, a floating-point number is $m \cdot 10^\alpha$ with $\alpha \in \mathbb Z$ and mantissa $m \in \{0\} \cup [0.1, 1)$ having $p$ decimal digits after the point; the rounding $[y]$ of a real $y$ is the closest floating-point number with precision $p$ based on the first $p + 1$ digits of $y$, with any fixed deterministic choice on ties that keeps the rounding log-bounded, mantissa-based, $(p+1)$-finite and sign preserving, and it acts on vectors coordinatewise. The *rounded orbit* is the sequence $x^{(0)} = [x]$, $x^{(t)} = [M x^{(t-1)}]$ for $t \ge 1$.

**Theorem (Lefaucheux, Ouaknine, Purser and Sharifi).** The floating-point point-to-point reachability problem is undecidable: no algorithm decides, given a linear dynamical system $(M, x)$ and a target $y \in \mathbb Q^d$, whether $y$ belongs to the rounded orbit.

The reduction uses precision $p = 1$ in base $10$ and matrices with negative entries. For non-negative matrices the same paper proves the full model-checking problem against semialgebraic predicates and $\omega$-regular specifications decidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for two-counter Minsky machines started with both counters at $0$. The linear dynamical system has two variables for each state of the machine; while the machine is in state $j$, the counter values are stored in the exponents of the two variables of state $j$ and all other variables are $0$, and every mantissa is $0$ or $1$ after rounding. Branching on a zero test uses filter functions: $\mathrm{filter}^+(u, v)$ is $v$ if $v \ge u$ and $0$ otherwise, $\mathrm{filter}^-(u, v)$ is $v$ if $v < u$ and $0$ otherwise, and for $u, v$ powers of $10$ they are computed by three and four linear operations with rounding (for example $u + v$, then subtracting $u$, then multiplying by $1.1$), which needs negative coefficients. The target is the vector encoding the halting state.

## Sources

- Engel Lefaucheux, Joël Ouaknine, David Purser and Mohammadamin Sharifi, "Model checking linear dynamical systems under floating-point rounding", in *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2023)*, Lecture Notes in Computer Science 13993, Springer, 2023, pp. 47–65, <https://doi.org/10.1007/978-3-031-30823-9_3>; read as arXiv:2211.04301v2, <https://arxiv.org/abs/2211.04301v2>: Definitions 1 to 3 and Problem 2 of Section 2, Theorem 1 with its proof sketch in Section 3 (Lemma 1 and Corollary 1 on the filter functions) and its full proof in Appendix A, and Theorem 2, of that version.

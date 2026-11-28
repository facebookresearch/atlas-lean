# Semilinear separating invariants for two rational matrices are undecidable

No algorithm decides, given two rational square matrices $A, B$ and rational points $x, y$, whether some semilinear set contains $x$, is closed under $A$ and $B$, and avoids $y$. Thus separating invariants in the semilinear domain cannot be decided even for unguarded affine programs with one location and two transitions.

**Theorem (Fijalkow, Lefaucheux, Ohlmann, Ouaknine, Pouly and Worrell).** The following problem is undecidable: given $d \ge 1$, matrices $A, B \in \mathbb{Q}^{d \times d}$ and points $x, y \in \mathbb{Q}^d$, does there exist a semilinear set $\mathcal{I} \subseteq \mathbb{R}^d$ with $x \in \mathcal{I}$, $A\mathcal{I} \subseteq \mathcal{I}$, $B\mathcal{I} \subseteq \mathcal{I}$ and $y \notin \mathcal{I}$?

The authors remark that their proof gives undecidability already for the fixed dimension $d = 336$, and for $d = 27$ if $\mathcal{I}$ is moreover required to be topologically closed (neither value is claimed optimal), and that the proof carries over to semialgebraic invariants and to semilinear sets with rational, algebraic or real coordinates. The proof uses two transitions. For a single rational matrix the same paper decides the existence of closed semilinear separating invariants with algebraic coordinates (its Theorem 3), and Fijalkow, Ohlmann, Ouaknine, Pouly and Worrell decided the semialgebraic case; the source does not settle the non-closed semilinear case for one matrix.

## Depends on

- [Semilinear invariant problem](semilinear-invariant-problem.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof first shows undecidability for robust instances, in which the target is not in the closure of the reachable set, by a reduction from the infinite Post correspondence problem ($\omega$-PCP) with nine pairs. Robustness means closedness of the invariant is no longer needed. The nine matrices of small dimension are then packed into two matrices of larger dimension, by the same construction that turns the nine $3 \times 3$ matrices of the [closed case](closed-semilinear-invariants-nine-3x3-matrices.md) into two $27 \times 27$ matrices. A good expansion links a page for the undecidability of the infinite Post correspondence problem.

## Sources

- Nathanaël Fijalkow, Engel Lefaucheux, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly and James Worrell, "On the Monniaux Problem in Abstract Interpretation", Static Analysis (SAS 2019), Lecture Notes in Computer Science 11822, pp. 162–180, 2019, <https://doi.org/10.1007/978-3-030-32304-2_9>; Theorem 1, Remark 2, Theorem 3, Theorems 9 and 10 and Section 4 of arXiv:1907.08257v1, <https://arxiv.org/abs/1907.08257v1>.

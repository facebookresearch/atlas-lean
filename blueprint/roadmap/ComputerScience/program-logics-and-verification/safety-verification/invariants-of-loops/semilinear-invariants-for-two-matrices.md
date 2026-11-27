# Semilinear separating invariants for two rational matrices are undecidable

No algorithm decides, given two rational square matrices $A, B$ and rational points $x, y$, whether some semilinear set contains $x$, is closed under $A$ and $B$, and avoids $y$. Thus separating invariants in the semilinear domain cannot be decided even for unguarded affine programs with one location and two transitions.

**Theorem (Fijalkow, Lefaucheux, Ohlmann, Ouaknine, Pouly and Worrell).** The following problem is undecidable: given $d \ge 1$, matrices $A, B \in \mathbb{Q}^{d \times d}$ and points $x, y \in \mathbb{Q}^d$, does there exist a semilinear set $\mathcal{I} \subseteq \mathbb{R}^d$ with $x \in \mathcal{I}$, $A\mathcal{I} \subseteq \mathcal{I}$, $B\mathcal{I} \subseteq \mathcal{I}$ and $y \notin \mathcal{I}$?

The authors remark that their proof gives undecidability already for the fixed dimension $d = 336$, and for $d = 27$ if $\mathcal{I}$ is moreover required to be topologically closed (neither value is claimed optimal), and that the proof carries over to semialgebraic invariants and to semilinear sets with rational, algebraic or real coordinates. Two transitions are needed: for a single rational matrix the same paper shows that the existence of a closed semilinear separating invariant with algebraic coordinates is decidable (its Theorem 3), and for semialgebraic invariants this had been shown earlier by Fijalkow, Ohlmann, Ouaknine, Pouly and Worrell.

## Depends on

- [Semilinear invariant problem](semilinear-invariant-problem.md)

## Proof depends on

None.

## Expansion

The proof first shows undecidability for robust instances, in which the target is not in the closure of the reachable set, by a reduction from the infinite Post correspondence problem ($\omega$-PCP) with nine pairs. Robustness means closedness of the invariant is no longer needed. The nine matrices of small dimension are then packed into two matrices of larger dimension, by the same construction that turns the nine $3 \times 3$ matrices of the [closed case](closed-semilinear-invariants-nine-3x3-matrices.md) into two $27 \times 27$ matrices. The infinite Post correspondence problem has no page here.

## Sources

- Nathanaël Fijalkow, Engel Lefaucheux, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly and James Worrell, "On the Monniaux Problem in Abstract Interpretation", Static Analysis (SAS 2019), Lecture Notes in Computer Science 11822, pp. 162–180, 2019, <https://doi.org/10.1007/978-3-030-32304-2_9>; Theorem 1, Remark 2, Theorem 3, Theorems 9 and 10 and Section 4 of arXiv:1907.08257v1, <https://arxiv.org/abs/1907.08257v1>.
- The same authors, "On the Monniaux Problem in Abstract Interpretation", Journal of the ACM 72(2), 51 pages, 2025, <https://doi.org/10.1145/3704632>; extended version, not read (the statements rest on the version read of the first source above).
- Nathanaël Fijalkow, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly and James Worrell, "Complete Semialgebraic Invariant Synthesis for the Kannan-Lipton Orbit Problem", Theory of Computing Systems 63(5), pp. 1027–1048, 2019, <https://doi.org/10.1007/s00224-019-09913-3>; decidability of semialgebraic separating invariants for a single matrix, cited in the prose; not read, the clause rests on Section 1 of the version read of the first source above.

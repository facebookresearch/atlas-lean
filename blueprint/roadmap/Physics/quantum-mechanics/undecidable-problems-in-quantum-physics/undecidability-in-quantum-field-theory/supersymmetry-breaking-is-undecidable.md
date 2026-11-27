# Supersymmetry breaking of two-dimensional supersymmetric Lagrangian theories is undecidable

No algorithm decides, for a given two-dimensional $\mathcal{N} = (2,2)$ supersymmetric Lagrangian theory, whether it breaks supersymmetry; a specific such theory breaks supersymmetry exactly when Zermelo–Fraenkel set theory with choice is consistent.

A two-dimensional $\mathcal{N} = (2,2)$ *Wess–Zumino model* is a supersymmetric Lagrangian theory of chiral superfields $\Phi_1, \ldots, \Phi_n$ determined by a holomorphic superpotential $W(\Phi_1, \ldots, \Phi_n)$. Its supersymmetric vacua are the solutions of the F-term equations $\partial W / \partial \Phi_j = 0$ for all $j$; the theory *breaks supersymmetry* when there is no supersymmetric vacuum.

**Theorem (Tachikawa).**

1. There is no algorithm which decides, for each two-dimensional $\mathcal{N} = (2,2)$ supersymmetric Lagrangian theory given to it, whether it breaks supersymmetry.
2. There is a specific two-dimensional $\mathcal{N} = (2,2)$ supersymmetric Lagrangian theory which breaks supersymmetry if and only if $\mathsf{ZFC}$ is consistent. In particular, if $\mathsf{ZFC}$ is consistent, then $\mathsf{ZFC}$ cannot prove that this theory breaks supersymmetry.

The theories used are Wess–Zumino models whose superpotentials are built from integer polynomials and the entire function $\sin 2\pi i X$.

## Depends on

- [Entire functions](../../../../Analysis/complex-analysis/entire-functions/growth-of-entire-functions-along-continua/entire.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)
- [Gödel's second incompleteness theorem, abstract Hilbert–Bernays–Löb form](../../../../Logic/proof-theory/g-del-s-incompleteness-theorems/hilbert-bernays-lob-second-incompletenes.md)

## Expansion

By the negative solution of Hilbert's tenth problem, a Turing machine $\xi$ gives a Diophantine equation $P_\xi(x_1, \ldots, x_k) = 0$ over $\mathbb{Z}$ that has an integer solution exactly when $\xi$ halts. Take the Wess–Zumino model with chiral superfields $Y, Z_1, \ldots, Z_k, X_1, \ldots, X_k$ and superpotential

$$
W_\xi = Y \, P_\xi(X_1, \ldots, X_k)^2 + \sum_{a=1}^{k} Z_a (\sin 2\pi i X_a)^2 .
$$

The equations $\partial W_\xi / \partial Z_a = 0$ force $X_a \in \mathbb{Z}$, the equation $\partial W_\xi / \partial Y = 0$ then forces $P_\xi = 0$, and the remaining equations $\partial W_\xi / \partial X_a = 0$ hold automatically. So the model breaks supersymmetry exactly when $P_\xi$ has no integer solution, that is, exactly when $\xi$ does not halt, and undecidability of halting gives clause 1. Taking for $\xi$ a machine that searches for a contradiction in $\mathsf{ZFC}$ gives the equivalence in clause 2, and Gödel's second incompleteness theorem gives its unprovability part. The source adds that the statement cannot be disproved in $\mathsf{ZFC}$ either, which needs more than the consistency of $\mathsf{ZFC}$ (for instance its soundness for such arithmetic statements).

## Sources

- Y. Tachikawa, "Undecidable problems in quantum field theory", International Journal of Theoretical Physics 62 (2023), no. 9, article 199, https://doi.org/10.1007/s10773-023-05357-1; read in arXiv:2203.16689v3 (Section 3.3, "Undecidability of supersymmetry breaking", of arXiv:2203.16689v3).

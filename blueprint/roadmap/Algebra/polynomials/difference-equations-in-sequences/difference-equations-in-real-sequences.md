# Consistency of difference equations in sequences of real numbers is undecidable

For a subfield of the real numbers, no algorithm decides whether a finite system of difference equations with coefficients in a computable subfield has a solution in sequences over that field, for one-sided and for two-sided sequences.

**Theorem (Pogudin–Scanlon–Wibmer).** Let $k$ be a field with $k \subseteq \mathbb{R}$, let $k_0 \subseteq k$ be a computable subfield, and let $M$ be $\mathbb{N}$ or $\mathbb{Z}$. There is no algorithm that decides, given a finite set $F$ of difference polynomials in finitely many unknowns with coefficients in $k_0$, whether the system $F = 0$ has a solution in $k^M$.

Conventions: difference polynomials, the rings $k^{\mathbb{N}}$ and $k^{\mathbb{Z}}$ with the shift, and solutions are as in the linked definitions; the number of unknowns and the orders of the shifts are part of the input. By contrast, the source recalls that for an algebraically closed difference field $K$ consistency of a finite system of difference equations in $K^{\mathbb{N}}$ is decidable, by an effective bound in the difference Nullstellensatz of Ovchinnikov, Pogudin and Scanlon; the proof below uses the order of $\mathbb{R}$ through sums of squares.

## Depends on

- [Difference rings and rings of sequences](difference-rings-and-equations-in-sequences.md)
- [Difference polynomials and their solutions](difference-polynomials-and-their-solutions.md)
- [Computable subfields](computable-subfields.md)
- [Field](../../rings-and-fields/field.md)
- [Predicates decidable by a single-tape Turing machine](../../../TheoryOfComputation/turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)
- [Lagrange's four-square theorem](../../../NumberTheory/quadratic-forms-sums-of-squares/sums-of-squares/lagrange-four-square-theorem.md)

## Expansion

The proof reduces Hilbert's tenth problem over $\mathbb{Z}$, which is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem applied to the halting set. First, the system

$$
X Y_1 = 0, \qquad Y_2 = Y_3^2 + Y_4^2 + Y_5^2 + Y_6^2, \qquad \sigma(Y_2) = Y_2 - 1 + Y_1
$$

forces the sequence $(x_i)_{i \in \mathbb{N}}$ to have infinitely many zeros: if $x_i \ne 0$ for all large $i$, then $y_{1,i} = 0$ and $y_{2,i+1} = y_{2,i} - 1$ for all large $i$, so $y_2$ eventually becomes negative, which a sum of four real squares cannot be. Conversely, every sequence with infinitely many zeros extends to a solution, with $y_2$ a nonnegative integer count-down between consecutive zeros, written as a sum of four squares by Lagrange's theorem. Given $P \in \mathbb{Z}[t_1, \dots, t_n]$, take $n + 1$ copies of this system with distinguished unknowns $X_0, \dots, X_n$ and add

$$
X_0 = P(X_1, \dots, X_n), \qquad (\sigma(X_j) - X_j)^2 = 1 \quad (1 \le j \le n).
$$

Each $x_j$, $j \ge 1$, moves by $\pm 1$ at every step and has a zero, so all its terms are integers, and $x_0$ has a zero, so $P$ has an integer zero. Conversely, from an integer zero $(a_1, \dots, a_n)$ one builds integer walks that return to $0$ and to $a_j$ infinitely often and pass through $(a_1, \dots, a_n)$ simultaneously infinitely often. The construction has rational coefficients, so it lies in $k_0[\sigma^i(\boldsymbol{X}) \mid i \in M]$ for every $k_0$. All the steps used here are linked or proved in the source.

## Sources

- Gleb Pogudin, Thomas Scanlon and Michael Wibmer, *Solving difference equations in sequences: universality and undecidability*, Forum of Mathematics, Sigma 8 (2020), e33, https://doi.org/10.1017/fms.2020.14; Theorem 3.6 of arXiv:1909.03239v2, proved in Section 4.2 there (Lemma 4.4 and the construction of $F_P$).

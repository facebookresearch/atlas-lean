# The Diophantine problem over the positive integers with addition and x·2^y is undecidable

There is no algorithm that decides whether a system of equations over the structure $\langle \mathbb{N}_{>0}; +, x \cdot 2^y, \le, 1 \rangle$ has a solution, although the corresponding problem with $x \mapsto 2^x$ in place of $x \cdot 2^y$ is decidable.

Let $\widetilde{N} = \langle \mathbb{N}_{>0}; +, x \cdot 2^y, \le, 1 \rangle$: the positive integers with addition, the binary operation $(x, y) \mapsto x \cdot 2^y$, the order $\le$ and the constant $1$. An equation over $\widetilde{N}$ is an atomic formula $s = t$ (or $s \le t$) between terms built from variables, $1$, $+$ and $x \cdot 2^y$. The *Diophantine problem* $\mathcal{DP}(\widetilde{N})$ asks, for a given finite system of such equations, whether it has a solution in positive integers.

**Theorem (Rybalov).** $\mathcal{DP}(\widetilde{N})$ is undecidable.

Conventions: the solutions range over $\mathbb{N}_{>0}$; multiplication of two variables is not a basic operation of $\widetilde{N}$. By Semenov's theorem the first-order theory of $\langle \mathbb{N}; +, x \mapsto 2^x, 1 \rangle$ is decidable, so its Diophantine problem is decidable; and the Diophantine problem over $\langle \mathbb{N}; +, \mid \rangle$ is decidable by Beltjukov and Lipshitz. As a consequence of the theorem, $\widetilde{N}$, a structure related to power circuits, is not an automatic structure, since automatic structures have decidable first-order theories.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For each $k$, solvability of polynomial systems over $\mathbb{N}$ reduces to solvability with all unknowns in $\mathbb{N}_{>k}$, by trying all assignments of the values $0, \dots, k$ to subsets of the unknowns; so Hilbert's tenth problem restricted to solutions greater than $1$ is undecidable. It then suffices to define multiplication of numbers greater than $1$ by a system of equations over $\widetilde{N}$. Divisibility is Diophantine because $m \mid n$ exactly when $2^m - 1 \mid 2^n - 1$, that is, when $2^n + z = z \cdot 2^m + 1$ for some $z$; the strict order is Diophantine through $x + z = y$. Further lemmas define the binary logarithm and squaring, and multiplication follows from $2z + x^2 + y^2 = (x + y)^2$. Rewriting a polynomial system in Skolem form, with equations $x_i = x_j x_k$, $x_i = x_j + x_k$, $x_i = x_j + 1$ and $x_i = x_j$, and replacing each multiplication by its definition, gives an equivalent system over $\widetilde{N}$. A good expansion links a page for the undecidability of Hilbert's tenth problem over $\mathbb{N}$, from the DPRM theorem and the undecidability of halting, from which Corollary 2.2 starts, and spells out Lemmas 2.3–2.8.

## Sources

- Alexander Rybalov, *On the Diophantine problem related to power circuits*, J. Groups Complex. Cryptol. 18 (2026), no. 1, https://doi.org/10.46298/jgcc.2026.18.1.17270; Theorem 2.9 in Section 2 of arXiv:2601.00835v4, with Lemma 2.1 and Corollary 2.2 (solutions in $\mathbb{N}_{>k}$) and Lemmas 2.3–2.8 (divisibility, order, logarithm, squaring and multiplication) in that section.

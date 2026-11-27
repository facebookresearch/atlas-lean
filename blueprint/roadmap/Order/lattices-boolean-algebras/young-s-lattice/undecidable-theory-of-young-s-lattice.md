# The elementary theory of Young's lattice is undecidable

The first-order theory of Young's lattice, as an ordered set, is undecidable and inherently non-finitely axiomatizable; with the constant [1]+[1] added, already its Σ₄ part is undecidable.

**Theorem (Wires).** The elementary (first-order) theory of [Young's lattice](young-s-lattice.md) $\mathbf Y = \langle \mathcal P, \le \rangle$ in the language of the order relation is undecidable and inherently non-finitely axiomatizable. Moreover, let $\mathbf Y^\ast = \langle \mathcal P, \le, [1] + [1] \rangle$ be Young's lattice with a constant for the partition $(1, 1)$; then the set of $\Sigma_4$ sentences true in $\mathbf Y^\ast$ is undecidable.

Here a $\Sigma_n$ sentence is one equivalent to a prenex sentence with $n$ alternating blocks of quantifiers beginning with an existential block. The constant is needed to break the symmetry of conjugation, since $[2]^\partial = [1] + [1]$. The same paper shows that $\mathbf Y^\ast$ has the maximal definability property: its definable relations are exactly the arithmetically definable ones under a suitable coding of partitions by natural numbers. It conjectures that the $\Sigma_1$ theory of $\mathbf Y$ is NP-complete and that the $\Sigma_1$ theory with constants for all partitions is undecidable.

## Depends on

- [Young's lattice](young-s-lattice.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof interprets $\langle \mathbb N, +, \times \rangle$ in $\mathbf Y^\ast$: the partitions $[n]$ with a single part represent the natural numbers, and the ternary relations of addition and multiplication restricted to them are defined by $\Pi_3$ formulas. Undecidability of the positive existential theory of $\langle \mathbb N, +, \times \rangle$ (Matiyasevich) then gives the undecidability of the $\Sigma_4$ theory of $\mathbf Y^\ast$. Since the elementary theory of a fixed structure is complete, general results on interpretations of arithmetic transfer this to undecidability and inherent non-finite axiomatizability of the theory of $\mathbf Y$; those interpretation results have no page here.

## Sources

- Alexander Wires, "Complexity in Young's lattice", *Annals of Pure and Applied Logic* 173(4), 2022, article 103075, doi:[10.1016/j.apal.2021.103075](https://doi.org/10.1016/j.apal.2021.103075); read as arXiv:1907.13360v1, <https://arxiv.org/abs/1907.13360v1>, whose numbering is used: Section 2 (prenex classes $\Sigma_n$), Theorem 3.15 and Theorem 3.16 in Section 3 ("Arithmetic"), Theorem 4.4 in Section 4, and Conjectures 5.1 and 5.3 in Section 5.

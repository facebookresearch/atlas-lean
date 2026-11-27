# Brin–Thompson group nV

For $n \ge 1$, the Brin–Thompson group $nV$ is the group of homeomorphisms of the product of $n$ Cantor sets that act, piece by piece on a finite partition into dyadic boxes, by replacing prefixes of the coordinates; $1V$ is Thompson's group $V$.

Let $C = \{0, 1\}^{\mathbb{N}}$ be the Cantor set of infinite binary sequences. For a finite binary word $\alpha$, the dyadic interval $I(\alpha) = \{\alpha\omega : \omega \in C\}$ is the set of sequences beginning with $\alpha$. For $n \ge 1$, a dyadic box in $C^n$ is a set $I(\alpha_1) \times \cdots \times I(\alpha_n)$. For two dyadic boxes the prefix replacement

$$
(\alpha_1\psi_1, \dots, \alpha_n\psi_n) \mapsto (\beta_1\psi_1, \dots, \beta_n\psi_n) \qquad (\psi_1, \dots, \psi_n \in C)
$$

is a bijection from $I(\alpha_1) \times \cdots \times I(\alpha_n)$ onto $I(\beta_1) \times \cdots \times I(\beta_n)$. The group $nV$ consists of all homeomorphisms $f\colon C^n \to C^n$ for which there is a partition of $C^n$ into finitely many dyadic boxes such that $f$ acts on each box of the partition as a prefix replacement.

## Depends on

- [Group](../../../group-basics/group.md)

## Proof depends on

None.

## Expansion

The images of the boxes of such a partition again partition $C^n$, so an element of $nV$ is described by a pair of numbered box partitions, which makes products, inverses and equality effectively computable; hence $nV$ has solvable word problem. The groups $nV$ are simple and finitely presented (Brin for $2V$; Hennig and Matucci in general), and $mV$ embeds in $nV$ for $m \le n$.

## Sources

- M. G. Brin, "Higher dimensional Thompson groups", Geometriae Dedicata 108 (2004), 163–192, https://doi.org/10.1007/s10711-004-8122-9; arXiv:math/0406046v1 (Section 2, the definition of $2V$ by numbered pattern pairs of dyadic rectangles, and Section 4.1, the groups $nV$ acting on $C^n$ through patterns of rectangular solids coded by $n$-tuples of binary words, of arXiv:math/0406046v1).
- J. Belk and C. Bleak, "Some undecidability results for asynchronous transducers and the Brin–Thompson group 2V", Transactions of the American Mathematical Society 369 (2017), no. 5, 3157–3172, https://doi.org/10.1090/tran/6963; arXiv:1405.0982v1 (Section 3 of arXiv:1405.0982v1: the definition of $2V$ and the effective computations with numbered pattern pairs).

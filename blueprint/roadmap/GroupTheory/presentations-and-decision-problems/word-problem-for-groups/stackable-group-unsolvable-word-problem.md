# A stackable group with unsolvable word problem

There exists a stackable group with unsolvable word problem; hence stackability, unlike algorithmic stackability, does not imply solvability of the word problem.

Stackability of a finitely generated group consists of a dynamical system on the paths of its Cayley graph that iteratively moves paths into a maximal tree; algorithmic stackability (and autostackability) adds computability (respectively regularity) conditions on this system, and implies that the word problem is solvable. There exists a stackable group with unsolvable word problem, and hence stackability does not imply algorithmic stackability (Theorem 5.1 of the source).

The source also proves that every HNN extension of a stackable group is stackable, and that stackable groups include groups whose Dehn function is not computable.

## Depends on

- [Solvable word problem](word-problem-solvable.md)
- [Group](../../group-basics/group.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](novikov-unsolvable.md)

## Expansion

Let $C = \langle Y \mid R \rangle$ be finitely presented with unsolvable word problem, $H = F(Y) \times F(Y')$, and $A \le H$ the Mihailova subgroup of pairs with the same image in $C$, finitely generated with undecidable membership. The example is the HNN extension $G = H *_A$ with the identity map on $A$, so the stable letter commutes with $A$: $H$, a direct product of free groups, is stackable, HNN extensions of stackable groups are stackable, and undecidable membership in $A$ makes the word problem of the extension unsolvable. Mihailova's theorem and the source's theorem that HNN extensions of stackable groups are stackable have no pages here.

## Sources

- S. Hermiller and C. Martínez-Pérez, "HNN extensions and stackable groups", Groups, Geometry, and Dynamics 12 (2018), no. 3, 1123–1158, https://doi.org/10.4171/GGD/467; read in arXiv:1605.06145v1, whose numbering is used here (Theorem 5.1 of arXiv:1605.06145v1).

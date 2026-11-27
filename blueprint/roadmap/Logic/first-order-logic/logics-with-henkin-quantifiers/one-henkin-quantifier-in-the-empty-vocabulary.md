# One Henkin quantifier in the empty vocabulary suffices for undecidability

There is a single Henkin quantifier whose addition to first-order logic with only equality already makes the set of valid sentences undecidable; explicitly, $\mathsf{H}_{12}$ and $\mathsf{E}_{10}$ are such quantifiers.

**Theorem (Zdanowski).** For the [Henkin quantifiers](henkin-quantifiers.md) $\mathsf{H}_n$ and $\mathsf{E}_n$:

1. there is $n$ such that the logics $L_\emptyset(\mathsf{H}_n)$ and $L_\emptyset(\mathsf{E}_n)$ are undecidable (Theorem 6);
2. the logics $L_\emptyset(\mathsf{H}_{12})$ and $L_\emptyset(\mathsf{E}_{10})$ are undecidable (Theorem 8).

Here $L_\emptyset(Q)$ is first-order logic with equality and no other non-logical symbols, extended by the single quantifier $Q$, and undecidability refers to its set of valid sentences. Before, undecidability in the empty vocabulary was known only for the infinite families $\mathsf{H}_\omega$ and $\mathsf{E}_\omega$ (Krynicki and Mostowski; Mostowski and Zdanowski).

## Depends on

- [Henkin quantifiers](henkin-quantifiers.md)

## Proof depends on

- [The uniform word problem for Thue systems is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-thue-wp.md)

## Expansion

The proof adapts Krynicki and Mostowski's reduction of the word problem for semigroups to the tautology problem. Fix a finitely presented semigroup $E$ over $\{a, b\}$ with undecidable word problem. A single Henkin prefix provides functions $f_a, f_b, \dots$ on the universe, and a formula under it expresses that these functions satisfy the defining relations of $E$ under composition; an instance $v = w$ then corresponds to a sentence of $L_\emptyset(Q)$ that is valid iff $E \models v = w$. For clause 2 the fixed semigroup is Tseitin's semigroup with five generators and seven relations, whose word problem is undecidable, which bounds the size of the quantifier.

## Sources

- K. Zdanowski, "One Henkin quantifier in the empty vocabulary suffices for undecidability", *Fundamenta Informaticae* 164(4):375–386, 2019, doi:10.3233/FI-2019-1774; read as arXiv:1612.07154v1, <https://arxiv.org/abs/1612.07154v1>: Theorems 6, 7 (Tseitin) and 8, and Sections 3 and 4 of arXiv:1612.07154v1.

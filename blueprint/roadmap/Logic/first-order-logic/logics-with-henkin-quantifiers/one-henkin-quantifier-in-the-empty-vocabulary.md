# One Henkin quantifier in the empty vocabulary suffices for undecidability

There is a single Henkin quantifier whose addition to first-order logic with only equality already makes the set of valid sentences undecidable; explicitly, $\mathsf{H}_{12}$ and $\mathsf{E}_{10}$ are such quantifiers.

**Theorem (Zdanowski).** For the [Henkin quantifiers](henkin-quantifiers.md) $\mathsf{H}_n$ and $\mathsf{E}_n$:

1. there is $n$ such that the logics $L_\emptyset(\mathsf{H}_n)$ and $L_\emptyset(\mathsf{E}_n)$ are undecidable (Theorem 6);
2. the logics $L_\emptyset(\mathsf{H}_{12})$ and $L_\emptyset(\mathsf{E}_{10})$ are undecidable (Theorem 8).

Here $L_\emptyset(Q)$ is first-order logic with equality and no other non-logical symbols, extended by the single quantifier $Q$, and undecidability refers to its set of valid sentences. Before, undecidability in the empty vocabulary was known only for the infinite families $\mathsf{H}_\omega$ and $\mathsf{E}_\omega$ (Krynicki and Mostowski; Mostowski and Zdanowski).

## Depends on

- [Henkin quantifiers](henkin-quantifiers.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Some finite Thue system has an undecidable word problem](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-eqv-gen.md)

## Expansion

The proof adapts Krynicki and Mostowski's reduction of the word problem for semigroups to the tautology problem. Fix one finitely presented semigroup $E$ over $\{a, b\}$ whose word problem (the set of equations $v = w$ between nonempty words that hold in every semigroup satisfying the defining relations of $E$) is undecidable; the reduction starts from this fixed word problem, not from the uniform one. A single Henkin prefix provides functions $f_a, f_b, \dots$ on the universe, and a formula under it expresses that these functions satisfy the defining relations of $E$ under composition; an instance $v = w$ then corresponds to a sentence of $L_\emptyset(Q)$ that is valid iff $E \models v = w$. For clause 2 the fixed semigroup is Tseitin's semigroup $C$ with generators $a, b, c, d, e$ and the seven relations $ac = ca$, $ad = da$, $bc = cb$, $bd = db$, $eca = ce$, $edb = de$, $cca = ccae$, whose word problem is undecidable (Theorem 7 of the source), which bounds the size of the quantifier. A good expansion links pages for Tseitin's semigroup and the undecidability of its word problem, which clause 2 uses, and for the encoding of a fixed semigroup's word problem by one Henkin quantifier.

## Sources

- K. Zdanowski, "One Henkin quantifier in the empty vocabulary suffices for undecidability", *Fundamenta Informaticae* 164(4):375–386, 2019, doi:10.3233/FI-2019-1774; read as arXiv:1612.07154v1, <https://arxiv.org/abs/1612.07154v1>: Theorems 6, 7 (Tseitin) and 8, and Sections 3 and 4 of arXiv:1612.07154v1.

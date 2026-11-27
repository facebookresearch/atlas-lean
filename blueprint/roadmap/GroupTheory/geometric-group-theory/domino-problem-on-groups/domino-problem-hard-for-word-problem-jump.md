# The domino problem of (G × Z) * H is hard for the jump of the word problem of G

If an infinite group $G$ has the special symbol property, then the origin-constrained domino problem of $G \times \mathbb{Z}$, and the domino problem of $(G \times \mathbb{Z}) * H$ for every non-trivial finite group $H$, are at least as hard as the halting problem relative to the word problem of $G$.

Let $G$ be a finitely generated group. Its word problem $\mathrm{WP}(G)$ is the set of words over a finite symmetric generating set that represent the identity, and $\mathrm{WP}(G)'$ is its Turing jump, the halting problem for Turing machines with oracle $\mathrm{WP}(G)$; a set is $\mathrm{WP}(G)'$-hard when it is at least as hard as this halting problem. The group $G$ has the special symbol property if the subshift

$$
X_{\le 1} = \{ x \in \{0, 1\}^G : x(g) = x(h) = 1 \Rightarrow g = h \}
$$

of configurations with at most one symbol $1$ is sofic, that is, the image of a subshift of finite type under a continuous map commuting with the translations. The origin-constrained domino problem is the set of pairs $(a, \mathcal{F})$ of a symbol $a$ and a finite set of forbidden patterns $\mathcal{F}$ such that no configuration of $X_{\mathcal{F}}$ has the symbol $a$ at the identity.

Let $G$ be an infinite group with the special symbol property. Then (Theorem 3.7 of the source):

1. the origin-constrained domino problem of $G \times \mathbb{Z}$ is $\mathrm{WP}(G)'$-hard;
2. for every non-trivial finite group $H$, the domino problem of the free product $(G \times \mathbb{Z}) * H$ is $\mathrm{WP}(G)'$-hard.

In particular these problems are undecidable for every infinite $G$ with the special symbol property; by Dahmani and Yaman, finitely generated free groups, finitely generated abelian groups, hyperbolic groups and poly-hyperbolic groups have it. The source does not specify the reducibility in the notion of hardness.

## Depends on

- [Domino problem of a finitely generated group](domino-problem-of-a-group.md)
- [Group](../../group-basics/group.md)
- [Solvable word problem](../../presentations-and-decision-problems/word-problem-for-groups/word-problem-solvable.md)
- [The Turing jump](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/jump.md)
- [Turing reducibility of predicates](../../../TheoryOfComputation/degrees-and-hierarchies/turing-degrees-and-the-turing-jump/turing-reducible-pred.md)

## Proof depends on

None.

## Expansion

The proof simulates a $G$-machine, a Turing machine whose head moves on $G$ by generators, in a sofic subshift of $G \times \mathbb{Z}$: the $G$-layer carries the tape and, by the special symbol property, at most one head; the $\mathbb{Z}$-direction is time. Forbidden patterns force consecutive rows to follow the transition function and forbid the final state, so a configuration with the initial state at the origin exists exactly when the machine does not halt. The halting problem of $G$-machines is $\mathrm{WP}(G)'$-hard. For the free product with a finite group $H$, an auxiliary layer forces a head to appear wherever a marker occurs, which removes the origin constraint.

## Sources

- N. Aubrun, S. Barbieri and M. Sablik, "A notion of effectiveness for subshifts on finitely generated groups", Theoretical Computer Science 661 (2017), 35–55, https://doi.org/10.1016/j.tcs.2016.11.033; arXiv:1412.2582v3 (Theorem 3.7, Corollary 3.6 on the halting problem of $G$-machines, and the special symbol property recalled from Dahmani and Yaman in Section 2, of arXiv:1412.2582v3).

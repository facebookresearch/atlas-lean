# The binary Post correspondence problem for torsion-free hyperbolic groups is undecidable

No algorithm decides, for a torsion-free hyperbolic group $\Gamma$ and two homomorphisms $g, h$ from the free group of rank two to $\Gamma$, whether some element outside $\ker g \cap \ker h$ is equalized by $g$ and $h$.

The binary Post correspondence problem for torsion-free hyperbolic groups is undecidable (Theorem 3.3 of the source): there is no algorithm that, given an instance $(\{a, b\}, \Gamma, g, h)$ with $\Gamma$ a torsion-free hyperbolic group given by a finite presentation and $g, h\colon F(a, b) \to \Gamma$ homomorphisms, decides whether $\mathrm{Eq}(g, h) / (\ker g \cap \ker h)$ is trivial.

Neither of the maps $g, h$ used in the proof is injective. By contrast, the classical binary Post correspondence problem for free monoids is decidable, the binary problem for free groups is open (at the time of the source), and the source proves the problem decidable for virtually nilpotent groups.

## Depends on

- [Post correspondence problem for a group](post-correspondence-problem-for-a-group.md)
- [Word-hyperbolic groups](../../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Group](../../../group-basics/group.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Take a two-generated torsion-free hyperbolic group $H$ with trivial abelianization and a torsion-free finitely presented group $Q$ with undecidable word problem. The Belegradek–Osin version of the Rips construction gives a torsion-free hyperbolic group $\Gamma$ with a normal subgroup $N$, a quotient of $H$ (so two-generated with trivial abelianization), and $\Gamma / N \cong Q$; membership in $N$ is undecidable. For $y \in \Gamma \setminus \{1\}$ let $g(a) = 1$, $g(b) = y$, and let $h(a), h(b)$ generate $N$. If $y \notin N$ then $\langle y \rangle \cap N = 1$, since $Q$ is torsion-free, and the quotient is trivial; if $y \in N$ then $y h(b)^{-1} \in [N, N]$ gives a word $U$ in the commutator subgroup of $F(a, b)$ with $Ub$ a solution. So deciding the instances decides membership in $N$.

## Sources

- L. Ciobanu, A. Levine and A. D. Logan, "Post's correspondence problem for hyperbolic and virtually nilpotent groups", Bulletin of the London Mathematical Society 56 (2024), no. 1, 159–175, https://doi.org/10.1112/blms.12921; read in arXiv:2211.12158v2 (Theorem 3.3 and its proof in Section 3 of arXiv:2211.12158v2).

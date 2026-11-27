# Post correspondence problem for a group

Post's correspondence problem for a group $\Gamma$ takes a finite alphabet $\Sigma$ and two homomorphisms $g, h$ from the free group on $\Sigma$ to $\Gamma$, and asks whether some $x$ with $g(x) = h(x)$ lies outside $\ker g \cap \ker h$.

An instance is a tuple $I = (\Sigma, \Gamma, g, h)$ where $\Sigma$ is a finite alphabet with free group $F(\Sigma)$, $\Gamma$ is a group given by a recursive presentation (finitely many generators and a recursive, for instance finite, set of relators), and $g, h\colon F(\Sigma) \to \Gamma$ are homomorphisms, given by the images of the letters of $\Sigma$ as words in the generators of $\Gamma$. The equalizer of $g$ and $h$ is the subgroup

$$
\mathrm{Eq}(g, h) = \{ x \in F(\Sigma) : g(x) = h(x) \}.
$$

The (kernel-based) Post correspondence problem asks: is the quotient $\mathrm{Eq}(g, h) / (\ker g \cap \ker h)$ trivial? Equivalently, is there no solution $x \in \mathrm{Eq}(g, h) \setminus (\ker g \cap \ker h)$? The binary version restricts to instances with $|\Sigma| = 2$, and for a class $\mathfrak{X}$ of recursively presented groups, the problem for $\mathfrak{X}$ restricts to instances with $\Gamma \in \mathfrak{X}$.

## Depends on

- [Group](../../../group-basics/group.md)
- [Recursively presented group](../../../orderable-groups/word-problem-for-orderable-groups/is-recursively-presented.md)

## Proof depends on

None.

## Expansion

When $g$ or $h$ is injective, $\ker g \cap \ker h$ is trivial and the problem asks for a non-trivial $x$ with $g(x) = h(x)$, as in the classical Post correspondence problem for free monoids. When neither map is injective and $\Sigma$ has at least two letters, $\ker g \cap \ker h$ contains the non-trivial subgroup $[\ker g, \ker h]$, so $\mathrm{Eq}(g, h)$ is never trivial, and quotienting by the common kernel discards these elementary solutions. The classical Post correspondence problem for free monoids is undecidable, while its binary version is decidable (Ehrenfeucht, Karhumäki and Rozenberg).

## Sources

- L. Ciobanu, A. Levine and A. D. Logan, "Post's correspondence problem for hyperbolic and virtually nilpotent groups", Bulletin of the London Mathematical Society 56 (2024), no. 1, 159–175, https://doi.org/10.1112/blms.12921; read in arXiv:2211.12158v2 (Section 2 of arXiv:2211.12158v2, definition of the kernel-based PCP, and Section 3 for the binary PCP and the PCP for a class of groups).

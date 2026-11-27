# Bounded cohomology of finitely presented groups is not computable

For each degree $d \ge 2$ and bound $D$, no algorithm decides from a finite presentation of a group $\Gamma$ whether $H^d_b(\Gamma; \mathbb{R})$ vanishes, has dimension at most $D$, or is large, nor whether $\Gamma$ is boundedly acyclic.

The bounded cohomology $H^*_b(\Gamma; \mathbb{R})$ of a group $\Gamma$ is the cohomology of the complex of bounded real-valued functions on $\Gamma^{n+1}$ that are invariant under the diagonal action of $\Gamma$, with the homogeneous coboundary. A group $\Gamma$ has large $n$-th bounded cohomology if $\dim_{\mathbb{R}} H^n_b(\Gamma; \mathbb{R}) \ge |\mathbb{R}|$, and is boundedly acyclic if $H^n_b(\Gamma; \mathbb{R}) = 0$ for all $n \ge 1$. Let $d \ge 2$ and $D \ge 0$ be integers. Then each of the following problems is undecidable: given a finite presentation $\langle S \mid R \rangle$, decide whether (Theorem 8.1 of the source)

1. $H^d_b(\langle S \mid R \rangle; \mathbb{R}) \cong 0$;
2. $\dim_{\mathbb{R}} H^d_b(\langle S \mid R \rangle; \mathbb{R}) \le D$;
3. $H^d_b(\langle S \mid R \rangle; \mathbb{R})$ is large;
4. $\langle S \mid R \rangle$ is boundedly acyclic.

The theorem also covers vanishing of the $d$-th $\ell^1$-homology and of its reduced version, and upper bounds on the bounded cohomological and bounded homological dimensions; the corresponding problems for finite simplicial complexes are undecidable as well (Corollary 8.2).

## Depends on

- [Group](../../group-basics/group.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

For a finitely presented torsion-free group $\Lambda$ with unsolvable word problem, the proof of the Adian–Rabin theorem gives an algorithm sending each word $w$ to a finite presentation $\Lambda_w$ with $\Lambda_w \cong 1$ exactly when $w = 1$ in $\Lambda$. In degrees 2 and 3 and for bounded acyclicity it suffices to take $\Gamma_w = \Lambda_w * \mathbb{Z}$: if $w = 1$ then $\Gamma_w \cong \mathbb{Z}$ is amenable, hence boundedly acyclic; otherwise $\Gamma_w$ is a non-elementary free product, hence acylindrically hyperbolic, and its second and third bounded cohomology are large. For higher degrees the source uses Weinberger's witness groups, iterated amalgamated products $\Gamma *_{\mathbb{Z}} \Lambda_w *_{\mathbb{Z}} \cdots *_{\mathbb{Z}} \Lambda_w$ of a fixed torsion-free witness $\Gamma$ with copies of $\Lambda_w$, which are trivial when $w = 1$ and otherwise proper amalgams over the amenable group $\mathbb{Z}$ that retain the bounded cohomology of $\Gamma$. The parts on bounded cohomological and homological dimension follow directly from the Adian–Rabin theorem (Theorem 8.4), since those bounds define Markov properties.

## Sources

- F. Fournier-Facio, C. Loeh and M. Moraschini, "Bounded cohomology of finitely presented groups: vanishing, non-vanishing, and computability", Annali della Scuola Normale Superiore di Pisa, Classe di Scienze (5) (2024), 1169–1202, https://doi.org/10.2422/2036-2145.202201_003; read in arXiv:2106.13567v3 (Theorem 8.1, Corollary 8.2 and Theorem 8.4 of arXiv:2106.13567v3).

# Bounded cohomology of finitely presented groups is not computable

For each degree $d \ge 2$ and bound $D$, no algorithm decides from a finite presentation of a group $\Gamma$ whether $H^d_b(\Gamma; \mathbb{R})$ vanishes, has dimension at most $D$, or is large, nor whether $\Gamma$ is boundedly acyclic.

The bounded cohomology $H^*_b(\Gamma; \mathbb{R})$ of a group $\Gamma$ is the cohomology of the complex of bounded real-valued functions on $\Gamma^{n+1}$ that are invariant under the diagonal action of $\Gamma$, with the homogeneous coboundary. A group $\Gamma$ has large $n$-th bounded cohomology if $\dim_{\mathbb{R}} H^n_b(\Gamma; \mathbb{R}) \ge |\mathbb{R}|$, and is boundedly acyclic if $H^n_b(\Gamma; \mathbb{R}) = 0$ for all $n \ge 1$. Let $d \ge 2$ and $D \ge 0$ be integers. Then each of the following problems is undecidable: given a finite presentation $\langle S \mid R \rangle$, decide whether (Theorem 8.1 of the source)

1. $H^d_b(\langle S \mid R \rangle; \mathbb{R}) \cong 0$;
2. $\dim_{\mathbb{R}} H^d_b(\langle S \mid R \rangle; \mathbb{R}) \le D$;
3. $H^d_b(\langle S \mid R \rangle; \mathbb{R})$ is large;
4. $\langle S \mid R \rangle$ is boundedly acyclic.

The theorem also covers vanishing of the $d$-th $\ell^1$-homology and of its reduced version, and upper bounds on the bounded cohomological and bounded homological dimensions. For finite simplicial complexes $X$, deciding whether $H^d_b(X; \mathbb{R}) \cong 0$, whether $\dim_{\mathbb{R}} H^d_b(X; \mathbb{R}) \le D$, whether $H^d_b(X; \mathbb{R})$ is large, whether the $d$-th $\ell^1$-homology of $X$ vanishes, and whether $X$ is boundedly acyclic are undecidable as well (Corollary 8.2).

## Depends on

- [Group](../../group-basics/group.md)
- [Group action on a set](../../permutation-groups/group-actions/group-action.md)
- [Finite abstract simplicial complex](../../../Combinatorics/polytopes-simplicial-complexes/rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

For a finitely presented torsion-free group $\Lambda$ with unsolvable word problem, the proof of the Adian–Rabin theorem gives an algorithm sending each word $w$ to a finite presentation $\Lambda_w$ with $\Lambda_w \cong 1$ exactly when $w = 1$ in $\Lambda$. In degrees 2 and 3 and for bounded acyclicity it suffices to take $\Gamma_w = \Lambda_w * \mathbb{Z}$: if $w = 1$ then $\Gamma_w \cong \mathbb{Z}$ is amenable, hence boundedly acyclic; otherwise $\Gamma_w$ is a non-elementary free product, hence acylindrically hyperbolic, and its second and third bounded cohomology are large. For degrees $d \ge 4$ the source uses Weinberger's witness groups $W(\Gamma, \Lambda, w) = \Gamma *_{\mathbb{Z}} \Lambda_w *_{\mathbb{Z}} \cdots *_{\mathbb{Z}} \Lambda_w$, iterated amalgamated products of a torsion-free finitely presented group $\Gamma$ with copies of $\Lambda_w$ (Construction 8.9): they are trivial when $w = 1$ and otherwise proper amalgams over the amenable group $\mathbb{Z}$, so that by Lemma 8.10 their $\ell^1$-Betti numbers are at least those of $\Gamma$. It then takes the product $\Pi_w = W(F_2, \Lambda, w) \times W(\Gamma, \Lambda, w)$, where $\Gamma$ is the fundamental group of an oriented closed connected hyperbolic $(d-2)$-manifold. If $w = 1$ then $\Pi_w \cong 1$; otherwise the product estimate for $\ell^1$-Betti numbers (Remark 2.7) with Lemma 8.10 gives $b^{\ell^1}_d(\Pi_w) \ge b^{\ell^1}_2(F_2) \cdot b^{\ell^1}_{d-2}(\Gamma) \ge |\mathbb{R}| \cdot 1$. Here $b^{\ell^1}_2(F_2) \ge \dim_{\mathbb{R}} H^2_b(F_2; \mathbb{R}) \ge |\mathbb{R}|$, because non-abelian free groups have large second bounded cohomology (Example 6.6(4) with Proposition 2.6(2)), and $b^{\ell^1}_{d-2}(\Gamma) > 0$ by Example 2.8. So $H^d_b(\Pi_w; \mathbb{R})$ is large by Proposition 2.6(1). The parts on bounded cohomological and homological dimension follow directly from the Adian–Rabin theorem (Theorem 8.4), since those bounds define Markov properties.

## Sources

- F. Fournier-Facio, C. Loeh and M. Moraschini, "Bounded cohomology of finitely presented groups: vanishing, non-vanishing, and computability", Annali della Scuola Normale Superiore di Pisa, Classe di Scienze (5) (2024), 1169–1202, https://doi.org/10.2422/2036-2145.202201_003; read in arXiv:2106.13567v3 (Theorem 8.1, Corollary 8.2, Theorem 8.4, Constructions 8.7 to 8.9, Lemma 8.10, Remark 2.7, Proposition 2.6, Example 2.8 and Example 6.6 of arXiv:2106.13567v3).

# Largeness and virtual first Betti number of torsion-free hyperbolic groups are undecidable

No algorithm decides, from a finite presentation of a torsion-free hyperbolic group, whether the group is large, or whether its virtual first Betti number is at least $d$, for any fixed $1 \le d \le \infty$.

For a group $\Gamma$ let $b_1(\Gamma) = \dim_{\mathbb{Q}} H_1(\Gamma; \mathbb{Q})$ and let the virtual first Betti number $vb_1(\Gamma) \in \{0, 1, 2, \dots\} \cup \{\infty\}$ be the supremum of $b_1(K)$ over the subgroups $K$ of finite index in $\Gamma$. There is a recursive sequence of finite presentations of torsion-free hyperbolic groups $\Gamma_n$ such that (Theorem 9.2 of the source)

1. for each $n$: $vb_1(\Gamma_n) > 0$ if and only if $vb_1(\Gamma_n) = \infty$, if and only if $\Gamma_n$ is large;
2. the set $\{ n \in \mathbb{N} : \Gamma_n \text{ is large} \}$ is recursively enumerable but not recursive.

Consequently, for every $1 \le d \le \infty$ there is no algorithm that determines whether a given torsion-free hyperbolic group $\Gamma$ has $vb_1(\Gamma) \ge d$, and no algorithm that determines whether it is large. By contrast, by Makanin's work on equations in free groups, it is decidable whether a finitely presented group maps onto a non-abelian free group.

## Depends on

- [Word-hyperbolic groups](../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Large group](large-group.md)
- [First Betti number of a group](../../free-groups/automorphisms-of-free-groups/finite-index-subgroups-of-automorphism-groups-of/first-betti-rank.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [Having a proper finite-index subgroup is undecidable for finitely presented groups](proper-finite-index-subgroup-undecidable.md)

## Expansion

Start from the recursive sequence of fundamental groups $G_n$ of compact non-positively curved square complexes $X_n$ for which $X_n$ has a proper connected finite-sheeted cover exactly when $\pi_1 X_n$ is large, and the set of $n$ with $\pi_1 X_n$ large is recursively enumerable but not recursive (Corollary 7.8, the strengthening of Theorem B). Apply the Belegradek–Osin version of the Rips construction (Theorem 9.1, quoted) with a fixed torsion-free non-elementary hyperbolic group $H$ with Property (T), such as a torsion-free uniform lattice in $\mathrm{Sp}(n,1)$: it outputs torsion-free hyperbolic groups $\Gamma_n$ with short exact sequences $1 \to N_n \to \Gamma_n \to G_n \to 1$, $N_n$ a quotient of $H$. Then $vb_1(G_n) > 0$ implies $\Gamma_n$ large, which implies $vb_1(\Gamma_n) = \infty$; conversely, a finite-index $K \le \Gamma_n$ mapping onto $\mathbb{Z}$ kills $N_n \cap K$, whose abelianization is finite by Property (T), so $vb_1(G_n) > 0$. The two consequences stated above are items (1) and (2) of Theorem D in the introduction, which the source derives from Theorem 9.2.

## Sources

- M. R. Bridson and H. Wilton, "The triviality problem for profinite completions", Inventiones Mathematicae 202 (2015), no. 2, 839–874, https://doi.org/10.1007/s00222-015-0578-8; arXiv:1401.2273v3 (Theorem D, Corollary 7.8, Theorem 9.1 and Theorem 9.2 of arXiv:1401.2273v3).

# Equations with abelian predicates are undecidable in non-abelian right-angled Artin groups

For every right-angled Artin group that is not abelian, in particular every free group of rank at least two, no algorithm decides whether a system of equations has a solution whose abelianization satisfies given linear constraints.

For a finite simple graph $\Gamma$ let $G\Gamma$ be the right-angled Artin group with the vertices of $\Gamma$ as generators and the commutation $uv = vu$ for each edge. If $G\Gamma$ is not abelian, that is, if $\Gamma$ is not a complete graph, then the Diophantine problem with abelian predicates $\mathcal{DP}(G\Gamma, \mathrm{ab})$ is undecidable (Theorem A, proved as Theorem 6.14, of the source). For a free group $F(\Sigma)$ with $|\Sigma| \ge 2$, both $\mathcal{DP}(F(\Sigma), \mathrm{ab})$ and the Diophantine problem with linear exponent-sum constraints are undecidable (Theorem 3.3).

## Depends on

- [Diophantine problem with abelian predicates](diophantine-problem-with-abelian-predicates.md)
- [Group](../../group-basics/group.md)
- [Artin group](../../presentations-and-decision-problems/braid-and-artin/artin-groups/artin-group.md)
- [Commutator subgroup of a group](../../commutators-and-engel-conditions/commutator-subgroup.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Abelianization of a group](../../commutators-and-engel-conditions/abelianization.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The proof interprets the ring $(\mathbb{Z}, +, \times)$ in $(G, \mathrm{ab})$ by positive existential formulas (PE-interpretability), which reduces Hilbert's tenth problem, undecidable by the DPRM theorem, to $\mathcal{DP}(G, \mathrm{ab})$. For two non-commuting generators $s_1, s_2$ the exponent sum $|g|_{s_i}$ is read off from the abelianization, multiples are expressed through centralizers of generators, and a technical lemma (Lemma 5.3) gives multiplication of exponent sums through equations defining sets of the form $\{(s_1 s_2^{k})^t\}$. In the free group the argument follows Büchi and Senger's encoding of arithmetic into word equations with abelian constraints.

## Sources

- L. Ciobanu and A. Garreta, "Group equations with abelian predicates", International Mathematics Research Notices 2024 (2024), no. 5, 4119–4159, https://doi.org/10.1093/imrn/rnad179; read in arXiv:2204.13946v1 (Theorem A in the introduction, Theorem 3.3, Lemma 5.3 and Theorem 6.14 of arXiv:2204.13946v1).

# Balanced bipartition cover bound under the multispecies coalescent

**Setting.** A rooted binary species tree on $k$ species has minimum internal branch length $T_{\min}$ in coalescent units. Gene trees $\mathcal G = \{G_1, \dots, G_n\}$ are sampled independently under the multispecies coalescent (one lineage per species). $\mathcal G$ is a *bipartition cover* if every bipartition (split) of the species tree is a split of at least one $G_j$. Let $g_{a,j}(T)$ be the probability that $a$ lineages in Kingman's coalescent have coalesced to $j$ lineages after time $T$.

**Theorem (balanced bound).** Define random variables $W_\ell$ recursively by $W_1 \equiv 1$ and, for $\ell \ge 2$,
$$\mathbb P(W_\ell = j) = \sum_{a \ge 1} \sum_{b \ge 1} \mathbb P(W_{\lfloor \ell/2 \rfloor} = a)\, \mathbb P(W_{\lceil \ell/2 \rceil} = b)\, g_{a+b,j}(T_{\min}),$$
the number of lineages leaving the root branch of a balanced $\ell$-taxon tree whose branches all have length $T_{\min}$. Put $w_\ell = \mathbb P(W_\ell = 1)$. For a target confidence $q \in (0,1)$, if
$$n \ge M_b(k, T_{\min}) := \inf\Bigl\{ n \in \mathbb N : \sum_{\ell=2}^{k-2} (1 - w_\ell)^n \le 1 - q \Bigr\},$$
then $\mathcal G$ is a bipartition cover with probability at least $q$, for every topology of the species tree. In particular it suffices that
$$n \ge \frac{\log\bigl(\tfrac{k-3}{1-q}\bigr)}{-\log\bigl(1 - w_{k-2}\bigr)} .$$

## Depends on

- [The multispecies coalescent](../multispecies-coalescent/gene-tree-prob.md)

## Expansion

A split below an internal species-tree node with $\ell$ descendant taxa is recovered whenever all their lineages coalesce before leaving the branch above that node, an event of probability at least the analogous probability for $\ell$ lineages entering a single branch of length $T_{\min}$. The earlier bound used the caterpillar-type worst case $g_{\ell,1}(T_{\min})$, treating all $\ell$ lineages as entering the last branch simultaneously. The improvement shows, using ultra-log-concavity preserved by the Kingman pure-death semigroup and likelihood-ratio ordering of convolutions and mixtures, that among all subtrees with $\ell$ taxa and branch lengths at least $T_{\min}$ the balanced tree minimises the probability of a single surviving lineage, so $w_\ell$ is a topology-free lower bound. A union bound over the at most $k-3$ nontrivial splits, with independence across gene trees, gives the sum condition; since $w_\ell$ decreases in $\ell$ the closed-form sufficient condition follows.

## Sources

- Z. McNulty, "An Improved Bipartition Cover Bound for the Multispecies Coalescent Model", arXiv:2604.09509 (2026), Theorem 1.1, Corollary 2.2 and Theorem 2.9, <https://doi.org/10.48550/arXiv.2604.09509>.

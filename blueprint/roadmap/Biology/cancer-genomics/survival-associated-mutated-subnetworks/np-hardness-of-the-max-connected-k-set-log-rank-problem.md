# NP-hardness of the max connected k-set log-rank problem

**Setting.** There are $m$ patients sorted by survival time, $t_i=i$, with no ties, censoring indicators $c_i\in\{0,1\}$ ($c_i=1$ if death is observed), and an $n\times m$ binary mutation matrix $M$ over a gene set $G$. For $S\subseteq G$ let $x^S_i=1$ if some gene of $S$ is mutated in patient $i$, and let $m_1=\sum_i x^S_i$. The log-rank statistic comparing mutated and unmutated patients is

$$
V(x^S)=\sum_{j=1}^m c_j\Bigl(x^S_j-\frac{m_1-\sum_{i<j}x^S_i}{m-j+1}\Bigr),
$$

with null standard deviation $\sigma(x^S,c)=\sqrt{m_1(m-m_1)}\,f(c)$, where $f(c)$ depends only on the censoring vector. The subnetwork score is $w(S)=V(x^S)/\sqrt{m_1(m-m_1)}$.

**Problems.** *Max k-set log-rank:* find $S\subseteq G$ with $|S|=k$ maximizing $w(S)$. *Max connected k-set log-rank:* additionally, given an interaction graph $I=(G,E)$, require $S$ to induce a connected subgraph.

**Statement.**

1. The max k-set log-rank problem is NP-hard.
2. The max connected k-set log-rank problem is NP-hard already on graphs that contain at least one vertex of degree $O(n^{1/c})$ for a constant $c>1$; in particular it is NP-hard on general graphs (take $I$ complete).

## Expansion

The score is not set-additive: a patient mutated in two genes of $S$ counts once, so $x^S$ is a coverage (union) indicator, and choosing $k$ genes to shape the union of patient sets is a max-coverage-type selection, which carries the hardness. Connectivity does not rescue tractability: attaching the hard unconstrained instance to a hub vertex of moderate degree makes every $k$-set through the hub feasible, so the hardness persists in sparse interaction networks with hubs, which is the regime of real protein interaction graphs.

## Sources

- Altieri F, Hansen TV, Vandin F. NoMAS: a computational approach to find mutated subnetworks associated with survival in genome-wide cancer studies. *Frontiers in Genetics* 10 (2019) 265. <https://doi.org/10.3389/fgene.2019.00265>. PMCID: PMC6468148. Section 2.1, Eq. (1), Theorems 1 and 2.

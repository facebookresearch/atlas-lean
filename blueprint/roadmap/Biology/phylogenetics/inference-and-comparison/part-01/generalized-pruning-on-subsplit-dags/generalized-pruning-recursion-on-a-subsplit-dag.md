# Generalized pruning recursion on a subsplit DAG

**Setting.** Let $X$ be a totally ordered taxon set. A *clade* is a nonempty subset of $X$; a *subsplit* $s=\{V,Z\}$ of a clade $W$ is an unordered pair of disjoint clades with $V\cup Z=W$ (plus the leaf subsplits $\{\{x\},\emptyset\}$ and the root subsplit $\rho=\{X,\emptyset\}$). Write $\acute s$ and $\grave s$ for the left (lexicographically smaller) and right clades of $s$. A *subsplit DAG* $D$ for a collection $\mathcal T$ of rooted binary topologies has the subsplits of the topologies in $\mathcal T$ as nodes and an edge $t\to s$ whenever the taxon set of $s$ is one of the two clades of $t$.

**Parameterization.** For each clade of each subsplit $t$ there is a probability distribution $P(s\mid t)$ over the child subsplits $s$ resolving that clade, so that a topology $\tau\in D$ has prior probability

$$P(\tau)=\prod_{t\to s\in\tau}P(s\mid t).$$

Each DAG edge $t\to s$ carries one branch length $\theta(t\to s)$ and the substitution model gives a transition matrix $P(\theta(t\to s))$. For a non-leaf subsplit $t$ let $\mathcal T_{\mathrm{leaf}}(t)$ be the set of rooted topologies on the taxa of $t$ with root bipartition $t$, and define the marginal partial likelihood vector

$$p(t)=\sum_{\tau^{\downarrow}\in\mathcal T_{\mathrm{leaf}}(t)}p(\tau^{\downarrow})\,P(\tau^{\downarrow}\mid t),$$

where $p(\tau^{\downarrow})$ is the Felsenstein partial likelihood at the root of $\tau^{\downarrow}$; at a leaf subsplit $p$ is the indicator vector of the observed state.

**Lemma 1 (rootward pass).** For every non-leaf subsplit $t$,

$$p(t)=\Big(\sum_{s_1:\acute t\to s_1}P(\theta(\acute t\to s_1))\,p(s_1)\,P(s_1\mid \acute t)\Big)\circ\Big(\sum_{s_2:\grave t\to s_2}P(\theta(\grave t\to s_2))\,p(s_2)\,P(s_2\mid \grave t)\Big),$$

where $\circ$ is the entrywise product. Hence all $p(t)$ are computed by one postorder traversal of $D$.

**Lemma 3 (per-edge marginal likelihood).** Let $P(t\to s)=\sum_{\tau\in D}P(\tau)\mathbf 1[t\to s\in\tau]$ and $P(\tau\mid t\to s)=P(\tau)\mathbf 1[t\to s\in\tau]/P(t\to s)$. With $r(\grave t)$ the analogous leafward (rootward-topology-marginalized) partial likelihood vector of the clade $\grave t$, the per-edge marginal likelihood

$$\ell(\grave t\to s;\theta)=\sum_{\tau\ni \grave t\to s}P(Y\mid\tau,\theta)\,P(\tau\mid \grave t\to s)$$

equals

$$\ell(\grave t\to s;\theta)=\frac{r(\grave t)^{\top}P(\theta(\grave t\to s))\,p(s)}{P(\grave t)},$$

and the same holds with $\acute t$ in place of $\grave t$. Multiplying over sites gives a composite likelihood for each branch length, optimizable one edge at a time.

## Depends on

- [Felsenstein's pruning recursion](../../../felsenstein-s-pruning-algorithm/prune.md)

## Expansion

Lemma 1: substitute the definition of $p(s_j)$ into the right-hand side and expand. A pair of leafward topologies below $s_1$ and $s_2$ joined at $t$ is in bijection with a leafward topology of $t$; the Felsenstein recursion factorizes $p(\tau_t^{\downarrow})$ as the entrywise product of the two propagated child vectors, and the prior factorizes as $P(s_1\mid\acute t)P(\tau_1\mid s_1)P(s_2\mid\grave t)P(\tau_2\mid s_2)$. Summing over children and their subtopologies is therefore a single sum over $\mathcal T_{\mathrm{leaf}}(t)$.

Lemma 3: for any $\tau$ containing $\grave t\to s$, pruning across that edge gives $P(Y\mid\tau,\theta)=r(\tau_t^{\uparrow})^{\top}P(\theta(\grave t\to s))\,p(\tau_s^{\downarrow})$, and the prior splits as $P(\tau_t^{\uparrow})P(s\mid\grave t)P(\tau_s^{\downarrow}\mid s)$. Dividing by $P(\grave t\to s)=P(\grave t)P(s\mid\grave t)$ and summing the rootward and leafward pieces separately yields $r(\grave t)$ and $p(s)$. When $D$ encodes a single tree both lemmas reduce to the classical two-pass pruning algorithm.

## Sources

- Jun SH, Nasif H, Jennings-Shaffer C, Rich DH, Kooperberg A, Fourment M, Zhang C, Suchard MA, Matsen FA, "A topology-marginal composite likelihood via a generalized phylogenetic pruning algorithm", Algorithms Mol Biol 2023 Jul 31;18:10, Equations (7)-(10), (22)-(26), Lemmas 1-3, <https://doi.org/10.1186/s13015-023-00235-1>, PMCID PMC10391877.

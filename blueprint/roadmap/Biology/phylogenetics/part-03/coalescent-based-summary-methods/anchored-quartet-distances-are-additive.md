# Anchored quartet distances are additive

Let $T$ be a tree on leaf set $\mathcal{L}$ with additive distance matrix $D_T$, and for a quartet $Q = \{a,b,u,v\}$ let $\tau(Q)$ be its quartet length (the length of the internal path of $T|_Q$) and write $ab.uv \in \mathcal{Q}_T$ when $T|_Q$ has topology $ab|uv$. Fix constants $\alpha, \beta > 0$ and an increasing function $f$ with $0 < f(x) < \beta$ for $x > 0$.

**Definition (anchored distances).** For two *anchor* leaves $u, v$ and $a, b \in \mathcal{L} \setminus \{u,v\}$,

$$D'_{uv}[a,b] = \begin{cases} \beta + \alpha\, \tau(\{a,b,u,v\}), & ab.uv \notin \mathcal{Q}_T,\\ \beta - f\big(\tau(\{a,b,u,v\})\big), & ab.uv \in \mathcal{Q}_T,\end{cases}$$

with single-anchored $D'_v[a,b] = \sum_{u \ne a,b,v} D'_{uv}[a,b]$ and all-pairs anchored $D'[a,b] = \sum_{v \ne a,b}\sum_{u \ne a,b,v} D'_{uv}[a,b]$.

**Theorem 1.** $D'_{uv}$ is an additive distance matrix on $\mathcal{L} \setminus \{u,v\}$ whose tree is topologically identical to $T|_{\mathcal{L}\setminus\{u,v\}}$; likewise $D'_v$ and $D'$ are additive on $\mathcal{L}\setminus\{v\}$ and $\mathcal{L}$ with the topologies of $T|_{\mathcal{L}\setminus\{v\}}$ and $T$.

**Theorem 2.** The all-pairs anchored maximum distance matrix $D''[a,b] = \max_{u,v \in \mathcal{L}\setminus\{a,b\}} \max\big(0, (D'_{uv}[a,b] - \beta)/\alpha\big)$ is additive and has the topology and the internal branch lengths of $T$.

**Multispecies coalescent specialization.** Let $p(ab.uv)$ be the probability that a gene tree drawn from the multispecies coalescent on species tree $T$ induces $ab|uv$. Taking $\beta = \ln 3$, $\alpha = 1$ and $f(x) = \ln(3 - 2e^{-x})$ in the definition gives

$$D^*_{uv}[a,b] = -\ln p(ab.uv)$$

(Lemma 1), and so (Theorem 3) the matrices $D^*_{uv}$, $D^*_v[a,b] = \sum_u -\ln p(ab.uv)$ and $D^*[a,b] = \sum_{v}\sum_{u} -\ln p(ab.uv)$ are additive and represent the true species tree topology on $\mathcal{L}\setminus\{u,v\}$, $\mathcal{L}\setminus\{v\}$ and $\mathcal{L}$. Replacing $p$ by empirical quartet frequencies in $k$ gene trees and running a consistent distance method (such as neighbor joining) gives a statistically consistent summary method as $k \to \infty$.

## Depends on

- [Multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/README.md)
- [Neighbor joining](../../neighbor-joining/README.md)

## Expansion

Under the multispecies coalescent, a quartet with internal species-tree length $\tau$ (coalescent units) has its matching gene-tree topology with probability $1 - \tfrac23 e^{-\tau}$ and each alternative with probability $\tfrac13 e^{-\tau}$. Hence $-\ln p(ab.uv) = \ln 3 + \tau$ when $ab|uv$ is not the species quartet, and $\ln 3 - \ln(3 - 2e^{-\tau})$ when it is, which is exactly the anchored formula with the stated $\alpha, \beta, f$. Theorem 1 therefore lets any consistent estimator of quartet topologies and quartet lengths be turned into pairwise distances whose tree is correct, even though the branch lengths are distorted. For $D''$, any two non-sister leaves $a,b$ admit anchors for which $ab|uv$ is not the quartet topology and the quartet length equals $d_T(a,b)$ minus the two terminal branches.

## Sources

- E. Sayyari, S. Mirarab, "Anchoring quartet-based phylogenetic distances and applications to species tree reconstruction", BMC Genomics 17 (Suppl. 10) (2016) 783, Definitions 1–2, Equations (1)–(7), Theorems 1–3 and Lemma 1, <https://doi.org/10.1186/s12864-016-3098-z>, PMCID PMC5123309.

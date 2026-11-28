# Every countable collection is non-uniformly generatable but not with membership queries alone

Let $\mathcal{C} = \{L_1, L_2, \dots\}$ be a countable collection of infinite languages over a countable set $U$. Every such collection is non-uniformly generatable: there is a generator such that for each $L_{i^*} \in \mathcal{C}$ and every enumeration of $L_{i^*}$, all outputs lie in $L_{i^*} \setminus S_t$ at every step $t$ with $|S_t| \ge \max(i^*, m_{\mathcal{C}}(L_{i^*}) + 1)$, where the non-uniform complexity

$$
m_{\mathcal{C}}(L_i) = \max\Big\{ \Big|\bigcap_{L \in \mathcal{C}'} L\Big| : \mathcal{C}' \subseteq \{L_1, \dots, L_i\},\ L_i \in \mathcal{C}',\ \Big|\bigcap_{L \in \mathcal{C}'} L\Big| < \infty \Big\}
$$

depends only on $L_{i^*}$ and $\mathcal{C}$, not on the enumeration. However, no deterministic algorithm that accesses the languages only through membership queries "is $w \in L_i$?" can, for every collection $\{L_0, L_1\}$ of just two languages, generate correctly from each $L_j$ once some number $t^*(\mathcal{C}, L_j)$ of distinct strings has been seen. In the model where the generator may also ask, at every step, whether a string of its choice belongs to the target, uniform generation is possible exactly for the collections of finite generation-feedback dimension.

## Proof sketch

At step $t$ the generator starts from $I = U$ and scans $L_1, \dots, L_t$ in order; whenever $L_i \supseteq S_t$ and $I \cap L_i$ is infinite it replaces $I$ by $I \cap L_i$, and finally it outputs an unseen string of $I$. So $I$ is always infinite and an intersection of languages containing $S_t$. Once $|S_t| \ge i^*$ the target is scanned, and when it is reached $I \cap L_{i^*}$ is an intersection of languages from $\{L_1, \dots, L_{i^*}\}$ that contains $L_{i^*}$ and the at least $m_{\mathcal{C}}(L_{i^*}) + 1$ strings of $S_t$, so it is infinite by definition of $m_{\mathcal{C}}$; from then on $I \subseteq L_{i^*}$. The lower bound constructs, against any deterministic membership-query algorithm, two languages adaptively from the algorithm's queries and outputs so that the required bounds $t^*(\mathcal{C}, L_0)$ and $t^*(\mathcal{C}, L_1)$ cannot both exist.

## Depends on

- [Closure dimension and uniform and non-uniform generatability](closure-dimension.md)

## Sources

- M. Charikar, C. Pabbaraju, "Exploring Facets of Language Generation in the Limit", COLT (2025), arXiv:2411.15364, Definition 6, Theorems 1, 2, 5, 6 and 7.
- J. Li, V. Raman, A. Tewari, "Generation through the Lens of Learning Theory", COLT (2025), arXiv:2410.13714, Corollary 3.6.

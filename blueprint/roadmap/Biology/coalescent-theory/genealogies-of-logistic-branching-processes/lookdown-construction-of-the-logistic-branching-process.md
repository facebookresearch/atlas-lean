# Lookdown construction of the logistic branching process

**Model.** In the logistic branching process with carrying-capacity parameter $K$, each of the $N^K(t)$ individuals gives birth at rate $b$ to $\ell \ge 1$ children with probability $p_\ell$, dies at rate $d + \frac{c}{K}N^K(t)$, and carries a neutral type in a compact Polish space $E$ that mutates with generator $\mathcal{Q}_K$.

**Modified lookdown particle system.** Record the population as an ordered vector $X^K(t) = (X_1(t),\dots,X_{N}(t)) \in \bigcup_n E^n$ of types at levels $1,\dots,N$, evolving by:
- **Births:** at rate $b\,p_\ell\,N$, choose $\ell + 1$ indices $j_1 < \dots < j_{\ell+1}$ uniformly from $\{1,\dots,N+\ell\}$; the particle at level $j_1$ is the parent and copies of its type are inserted at levels $j_2,\dots,j_{\ell+1}$, the other particles keeping their relative order;
- **Deaths:** at rate $N(d + \frac{c}{K}N)$ the particle at the highest level is removed;
- **Mutation:** each particle's type moves independently with generator $\mathcal{Q}_K$.

**Theorem (lookdown representation).** The empirical measure $\sum_{i=1}^{N^K(t)}\delta_{X_i^K(t)}$ has the law of the logistic branching process. Moreover, if $(X_1^K(0),\dots,X_{N^K(0)}^K(0))$ is exchangeable, then $(X_1^K(t),\dots,X_{N^K(t)}^K(t))$ is exchangeable for every $t > 0$; consequently, given $N^K \ge k$, the genealogy of a uniform sample of size $k$ has the law of the coalescent induced by the first $k$ levels.

**Theorem (forward limits).** Let $n_* = (bm - d)/c$ with $m = \sum_\ell \ell p_\ell$, $m^{(2)} = \sum_\ell \ell^2 p_\ell$, $bm > d$, and suppose $r_K\mathcal{Q}_K$ converges to a generator $\mathcal{Q}$, with $r_K$ as below. Then, in the Skorokhod space $D_{E^\infty}[0,T]$:
1. if $\sum_\ell p_\ell\,\ell^{2+\delta} < \infty$, $(X^K(Kt))_t$ converges to the lookdown representation of the Fleming–Viot process with mutation $\mathcal{Q}$ and effective population size $N_e = n_*/(b(m + m^{(2)}))$;
2. if $p_\ell \sim p_0\,\ell^{-1-\alpha}$, $\alpha \in (1,2)$, $(X^K(K^{\alpha-1}t))_t$ converges to the lookdown representation of the $(\Lambda,\mathcal{Q})$-Fleming–Viot process with $\Lambda(du) = b\,p_0\,n_*^{1-\alpha}(1-u)^{\alpha-1}u^{1-\alpha}\,du$;
3. if $p_\ell\,\ell^2 \to p_0$, $(X^K(t))_t$ converges to the lookdown representation of the $(\Lambda,\mathcal{Q})$-Fleming–Viot process with $\Lambda(du) = b\,p_0\,du$, the dual of the Bolthausen–Sznitman coalescent.

## Depends on

- [Infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process](../../coalescent-theory/coalescents/infinite-lookdown-de-finetti-limit-and-lambda-fl.md)

## Expansion

The births follow Donnelly and Kurtz's type-II lookdown rule: the parent is always the lowest of the participating levels, so information flows only upward and the bottom levels carry the genealogy. Placing offspring at uniformly chosen levels and always killing the top particle keeps the level labels exchangeable, so projecting out the order recovers the branching process with competition. Because competition pins the population size near $Kn_*$, levels below any fixed height see reproduction events at the rates of a fixed-size population; under the stated time changes these rates converge to the pairwise-merger, Beta or uniform $\Lambda$ rates, and the particle system converges level by level to the limiting lookdown process.

## Sources

- Ruairi Garrett and Julio Ernesto Nava Trejo, "Genealogies under logistic growth", arXiv:2509.05217 (2025), Section 2 (Theorem 2.1 and Lemma 2.2) and Theorem 1.9, <https://doi.org/10.48550/arXiv.2509.05217>.

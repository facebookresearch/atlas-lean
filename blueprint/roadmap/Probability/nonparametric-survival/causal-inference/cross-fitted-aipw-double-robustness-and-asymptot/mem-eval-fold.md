# Mem eval Fold

Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. For all $n, i \in \mathbb{N}$ and every fold $k$,

$$i \in \mathrm{evalFold}(n, k) \iff i < n \ \text{and}\ \mathrm{fold}(n, i) = k,$$

where $\mathrm{evalFold}(n, k)$ is the set of evaluation indices of fold $k$ at sample size $n$.

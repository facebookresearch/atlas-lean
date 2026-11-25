# Train Fold

Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. For $n \in \mathbb{N}$ and a fold $k$, the training indices of fold $k$ at sample size $n$ are

$$\mathrm{trainFold}(n, k) = \{\, i \in \{0, \dots, n-1\} : \mathrm{fold}(n, i) \ne k \,\}.$$

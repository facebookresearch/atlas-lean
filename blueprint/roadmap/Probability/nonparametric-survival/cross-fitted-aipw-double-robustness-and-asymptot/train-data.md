# Train Data

Let $K \in \mathbb{N}$ and let $\mathrm{fold} : \mathbb{N} \to \mathbb{N} \to \{0, \dots, K-1\}$ be a fold assignment, $\mathrm{fold}(n, i)$ being the fold of unit $i$ at sample size $n$. Given observations $W_i : \Omega \to \mathcal{W}$, $i \in \mathbb{N}$, the training data of fold $k$ at sample size $n$ is the map

$$\Omega \to \mathcal{W}^{\mathrm{trainFold}(n, k)}, \qquad \omega \mapsto \bigl(W_i(\omega)\bigr)_{i \in \mathrm{trainFold}(n, k)},$$

where $\mathrm{trainFold}(n, k) = \{ i < n : \mathrm{fold}(n, i) \ne k \}$. Nuisances for fold $k$ are fitted on these observations only.

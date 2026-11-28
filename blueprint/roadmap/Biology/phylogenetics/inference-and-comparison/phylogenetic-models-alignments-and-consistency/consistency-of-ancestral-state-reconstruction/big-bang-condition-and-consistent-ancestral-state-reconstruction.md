# Big bang condition and consistent ancestral state reconstruction

**Setting.** Let $(\mathcal T_n)_{n\ge1}$ be a nested sequence of rooted phylogenetic trees with edge lengths ($\mathcal T_n$ is a subtree of $\mathcal T_{n+1}$, and the root is fixed) whose heights are uniformly bounded. A trait evolves from the root state along the branches and is observed at the leaves $\partial\mathcal T_n$; the task is to estimate the root state. Three trait models are considered:
- *Brownian motion (BM):* leaf values are Gaussian with mean the root value $\mu$ and covariance $\sigma^2\mathbf V_n$, where $(\mathbf V_n)_{ij}$ is the length of the shared root-to-leaf path of leaves $i$ and $j$;
- *regular discrete models:* finite-state continuous-time Markov chains along the branches (with the regularity assumptions of Fan and Roch);
- *threshold model:* a discrete character obtained by thresholding an underlying Brownian liability.

For $s > 0$ let $\mathcal T(s)$ be the tree truncated at distance $s$ from the root. The sequence satisfies the **big bang condition** if $|\partial\mathcal T_n(s)| \to \infty$ as $n\to\infty$ for every $s > 0$: arbitrarily close to the root there are eventually arbitrarily many lineages.

**Theorem.** For nested trees of bounded height:
1. The big bang condition holds if and only if $\mathbf 1^\top \mathbf V_n^{-1}\mathbf 1 \to +\infty$.
2. Either condition is necessary and sufficient for the existence of a consistent estimator of the ancestral (root) state under the BM model, under regular discrete models and under the threshold model.

Under BM, $\mathbf 1^\top\mathbf V_n^{-1}\mathbf 1 \to \infty$ is also exactly the condition for the maximum-likelihood estimator $\hat\mu_n = (\mathbf 1^\top\mathbf V_n^{-1}\mathbf 1)^{-1}\mathbf 1^\top\mathbf V_n^{-1}\mathbf X$ to be consistent, since $\operatorname{Var}(\hat\mu_n) = \sigma^2/(\mathbf 1^\top \mathbf V_n^{-1}\mathbf 1)$. For the threshold model, bounded $\mathbf 1^\top\mathbf V_n^{-1}\mathbf 1$ rules out any consistent estimator. Without bounded heights the equivalence fails, and neither condition suffices for discrete models.

## Proof sketch

$\mathbf 1^\top\mathbf V_n^{-1}\mathbf 1$ is the Fisher information about $\mu$ per unit $\sigma^{-2}$, an "effective number of independent leaves". If the big bang condition holds, choosing one leaf below each of many lineages present at depth $s$ gives nearly independent observations whose shared path has length at most $s$, so the information is at least of order $|\partial\mathcal T_n(s)|$ minus a correction that vanishes as $s \to 0$. Conversely, if $|\partial\mathcal T_n(s)|$ stays bounded for some $s$, all leaves descend from finitely many depth-$s$ ancestors, whose states carry noise of variance at least of order $s$ that no number of leaves can average out, so the information stays bounded and no estimator (BM, discrete or threshold) can be consistent.

## Sources

- Lam Si Tung Ho and Vu Dinh, "When can we reconstruct the ancestral state? A unified theory", *Theoretical Population Biology* 148 (2022), 22–27, <https://doi.org/10.1016/j.tpb.2022.09.001>. Preprint version: arXiv:2111.07445 (2021), main theorem, BM necessity and big-bang theorems, threshold-model theorem, building on Ané (2008) and Fan and Roch (2018), <https://doi.org/10.48550/arXiv.2111.07445>.

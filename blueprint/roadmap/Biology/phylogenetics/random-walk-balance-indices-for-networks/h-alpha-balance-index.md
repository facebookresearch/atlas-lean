# The H-alpha balance index of a phylogenetic network

**Definition.** Let $G$ be a finite rooted phylogenetic network with leaf set $\mathcal L_G$, and let $p_\ell$ be the probability that the simple random walk started at the root, moving at each step to a uniformly chosen child, ends at leaf $\ell$. For $\alpha > 0$, $\alpha \ne 1$,
$$H_\alpha(G) = \frac{1}{1 - 2^{1-\alpha}} \sum_{\ell \in \mathcal L_G} p_\ell\bigl(1 - p_\ell^{\alpha - 1}\bigr) = \frac{1 - \sum_{\ell} p_\ell^\alpha}{1 - 2^{1-\alpha}},$$
and $H_1(G) = \lim_{\alpha \to 1} H_\alpha(G) = -\sum_\ell p_\ell \log_2 p_\ell = B_2(G)$. Also $H_0 = |\mathcal L_G| - 1$ and $H_2$ is twice the Gini–Simpson index of $(p_\ell)$.

**Theorem.**
1. *Grafting.* If $G$ is obtained by identifying the root of $G_2$ with a leaf $\ell$ of $G_1$, then $H_\alpha(G) = H_\alpha(G_1) + p_{\ell,G_1}^{\alpha} H_\alpha(G_2)$. In particular grafting a cherry on $\ell$ adds $p_\ell^\alpha$, and grafting $G', G''$ on the two leaves of a cherry gives $1 + 2^{-\alpha}(H_\alpha(G') + H_\alpha(G''))$.
2. *Binary trees.* For a binary tree $T$ with root $\rho$, $H_\alpha(T) = 2^{\alpha-1} \sum_{v \ne \rho} 2^{-\alpha \delta_v} = 2^{\alpha - 1}\sum_{k \ge 1} 2^{-\alpha k} Z_k(T)$, where $\delta_v$ is the depth of $v$ and $Z_k(T)$ the number of vertices at depth $k$; as $\alpha \downarrow 0$ the first-order term is an affine function of the Sackin index.
3. *Extremes over all networks with $n$ leaves.* $\inf H_\alpha = 0$ and $\max H_\alpha = \dfrac{1 - n^{1-\alpha}}{1 - 2^{1-\alpha}}$, attained exactly when all $p_\ell = 1/n$.
4. *Binary trees with $n$ leaves.* $H_\alpha(\mathrm{Cat}(n)) \le H_\alpha(T) \le H_\alpha(\mathrm{CB}(m)) + (n - 2^{m})\,2^{-\alpha m}$, $m = \lfloor \log_2 n \rfloor$, with $\mathrm{Cat}(n)$ the caterpillar and $\mathrm{CB}(m)$ the complete binary tree of height $m$. The same bounds hold for temporal tree-child networks when $\alpha \le 1$, and every tree-child network satisfies $H_\alpha(N) \ge H_\alpha(\mathrm{FCat}(n))$ for the fat caterpillar.
5. If all $p_\ell \le 1/2$, $H_\alpha(G)$ is nonincreasing in $\alpha$; for $1 < \alpha < \beta$, $H_\alpha(G) \le \frac{1 - 2^{1-\beta}}{1 - 2^{1-\alpha}} H_\beta(G)$.

## Expansion

$H_\alpha$ is a Tsallis-type entropy of the leaf-hitting distribution, normalised so that a cherry has index $1$. The grafting identity follows because the walk reaches the grafted subnetwork with probability $p_\ell$ and then distributes that mass as in $G_2$, and $\sum_{\ell'} (p_\ell q_{\ell'})^\alpha = p_\ell^\alpha \sum q_{\ell'}^\alpha$. Hence the index of a network decomposes over its biconnected components, which reduces extremal questions to small blocks. Concavity of $x \mapsto x - x^\alpha$ gives the maximum at the uniform distribution; small values come from very unbalanced leaf masses.

## Sources

- F. Bienvenu, J.-J. Duchamps, H. Maffioli, "A parameterized family of balance indices for phylogenetic networks", arXiv:2606.24562 (2026), definition of $H_\alpha$ in Section 1, Propositions 1.2, 1.5, 1.8 and 1.10, Corollaries 1.6 and 1.7, Theorems 1.11, 1.12 and 1.14, <https://doi.org/10.48550/arXiv.2606.24562>.

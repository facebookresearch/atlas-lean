# Asymptotic count of rooted binary phylogenetic networks with $k$ reticulations

**Setting.** Let $\mathcal{P}_{\ell,k}$ be the set of rooted binary phylogenetic networks with $\ell$ labelled leaves and $k$ reticulation vertices (in-degree $2$, out-degree $1$), with no parallel edges and no further structural restriction (not necessarily tree-child, normal or of bounded level). For $k=1$, $|\mathcal{P}_{\ell,1}| = \ell\,(2\ell)!/(2^{\ell}\ell!) - 2^{\ell-1}\ell!$.

**Theorem (three-term asymptotics).** Uniformly for $1 \le k = o(\sqrt{\ell})$,

$$|\mathcal{P}_{\ell,k}| = \binom{\ell}{k}\sqrt{2}\, e^{-\ell}\,(2\ell)^{\ell+k-1}\Big(1 - \frac{\sqrt{\pi}\,k}{2\sqrt{\ell}} + \frac{62k^2-74k+11}{24\,\ell} + O\Big(\frac{k^3}{\ell^{3/2}} + \frac{k^4}{\ell^2}\Big)\Big).$$

**Theorem (rarity of symmetry).** For every fixed $k \ge 2$, the probability that a uniformly random network in $\mathcal{P}_{\ell,k}$ has a nontrivial leaf-fixing automorphism group is $\frac{k(k-1)}{4\ell^3}\big(1+O(\ell^{-1/2})\big)$. Automorphism groups of such networks are $2$-groups.

## Expansion

Writing $|\mathcal{P}_{\ell,k}| = W_k(\ell) + D_k(\ell)$, the weighted count $W_k(\ell) = \sum_N 1/|\mathrm{Aut}(N)|$ satisfies a recursion over the source layers of the tree-component decomposition whose exponential generating function is a Laurent polynomial in $u=\sqrt{1-2x}$. Coefficient extraction gives terms of the form $A(\ell)(2\ell-N-2)!! - B(\ell)2^{\ell}\ell!$; the dominant double-factorial term together with Stirling's formula yields the leading factor $\binom{\ell}{k}\sqrt2 e^{-\ell}(2\ell)^{\ell+k-1}$ and its corrections, while the defect $D_k(\ell)$ is of relative order $\ell^{-3}$.

## Sources

- J. Batle, "Exact and asymptotic enumeration of unrestricted binary phylogenetic networks through automorphism weights", arXiv:2610.03856, Corollary 6.9 and Theorem 6.13. <https://doi.org/10.48550/arXiv.2610.03856>

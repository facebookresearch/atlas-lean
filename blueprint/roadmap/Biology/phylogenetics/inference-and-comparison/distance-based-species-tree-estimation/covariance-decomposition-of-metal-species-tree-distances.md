# Covariance decomposition of METAL species-tree distances

**Setting.** Under the multispecies coalescent (MSC) on a species tree $\mathcal S$ with leaf set $L$, $m$ independent genes have gene trees $G^{(1)},\dots,G^{(m)}$; $g^{(i)}_{ab}$ is the path length between leaves $a,b$ in $G^{(i)}$. Along each gene tree, $K$ sites evolve independently under the Jukes-Cantor model with rate $\mu$, normalized so that two leaves at gene-tree distance $g$ differ at a site with probability $\tfrac34(1-e^{-\mu g})$. The **METAL** distance $\hat d_{ab}$ is the average over genes and sites of the indicator that $a$ and $b$ differ (normalized Hamming distance); STEAC averages per-gene Jukes-Cantor-corrected distances $\hat g^{(i)}_{ab}=-\mu^{-1}\log(1-\tfrac43\hat p^{(i)}_{ab})$, and GLASS takes minima of gene-tree distances. Each gives a species-tree estimate by hierarchical clustering. For pairs $ab,cd$, $\delta^{(i)}_{ab,cd}$ is the length of the intersection of the $a$-$b$ and $c$-$d$ paths in $G^{(i)}$, and $\Sigma_{\mathrm{total}}\in\mathbb R^{\binom n2\times\binom n2}$ is the covariance matrix of $(\hat d_{ab})$.

**Proposition 4 (covariance decomposition).** $\Sigma_{\mathrm{total}}=\frac1m\Sigma_{\mathrm{coal}}+\frac1{mK}\Sigma_{\mathrm{sub}}$, where

$$(\Sigma_{\mathrm{coal}})_{ab,cd}=\tfrac9{16}\,\mathrm{Cov}\bigl(e^{-\mu g^{(1)}_{ab}},e^{-\mu g^{(1)}_{cd}}\bigr),\qquad (\Sigma_{\mathrm{sub}})_{ab,cd}=\tfrac3{16}\,\mathbb E\Bigl[e^{-\mu(g_{ab}+g_{cd})}\bigl(e^{2\mu\delta_{ab,cd}}+2e^{\mu\delta_{ab,cd}}-3\bigr)\Bigr],$$

the expectation being over a gene tree under the MSC; all three matrices are positive semidefinite. Coalescent (gene-tree) variability is reduced only by adding genes, substitution noise by adding genes or sites.

**Proposition 2 (interpolation).** With exact gene trees and a common hierarchical clustering method, the METAL topology tends to the STEAC topology as $\mu\to0$ and to the GLASS topology as $\mu\to\infty$ (for single or complete linkage, assuming GLASS minima are unique).

**Proposition 3 (positive correlation).** Under the MSC, $\mathrm{Cor}(g^{(1)}_{ab},g^{(1)}_{cd})\ge\mathrm{Cor}(e^{tg^{(1)}_{ab}},e^{tg^{(1)}_{cd}})\ge0$ for all $t\le0$.

**Proposition 6 (STEAC breakdown).** The delta-method variance of the STEAC per-gene estimate $\hat g_{ab}$ is finite if and only if $\mu<1/4$; for $\mu\ge1/4$ each gene has positive probability $p=\mathbb P(\hat p^{(i)}_{ab}\ge3/4)$ of an infinite estimate, so the STEAC distance is finite with probability $(1-p)^m\to0$ as the number of genes grows.

## Expansion

Conditioning on the gene trees and applying the law of total covariance splits the METAL covariance into the variance of the conditional mean $\tfrac34(1-e^{-\mu g})$ (coalescent part) and the expected conditional covariance of site indicators (substitution part). Two site indicators for pairs $ab$ and $cd$ are dependent only through mutations on the shared path segment of length $\delta$, which produces the factor $e^{2\mu\delta}+2e^{\mu\delta}-3$, vanishing at $\delta=0$. As $\mu\to0$, $1-e^{-\mu g}\approx\mu g$, so averaging is order-equivalent to averaging coalescent distances (STEAC); as $\mu\to\infty$, $e^{-\mu g}$ is dominated by the smallest $g$ among genes, so the ranking of distances follows the minima used by GLASS. For a star species tree the covariance matrices have a three-value structure whose spectrum is explicit, with the all-ones vector as leading principal component (Proposition 7).

## Sources

- G. Aliatimis, R. Yoshida, B. Boyaci, J. A. Grant, "Covariance decomposition for distance based species tree estimation", *BMC Bioinformatics* 27(1) (2026), 228, Propositions 2-4, 6 and 7, <https://doi.org/10.1186/s12859-026-06495-z> (preprint arXiv:2506.16425).

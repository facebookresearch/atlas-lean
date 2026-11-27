# Consistency of likelihood ancestral state reconstruction on star trees with unknown edge lengths

**Setting.** A star tree has $n$ leaves attached directly to the root by edges of unknown lengths $t_1,\dots,t_n$. At each leaf one observes $N$ sites, which evolve independently from the root sequence $\rho^*=(\rho_1^*,\dots,\rho_N^*)\in\{1,\dots,c\}^N$ under the **proportional (Felsenstein-81-type) model**

$$P_{ij}(s)=\pi_j(1-s)+\mathbf 1_{\{i=j\}}s,\qquad s=e^{-\mu t}\in(0,1],$$

with known stationary distribution $\pi>0$. Assume $\liminf_n\bar s>0$, where $\bar s=\frac1n\sum_ks_k$; for example, this holds for i.i.d. edge lengths with finite mean. Let $y_k=(y_{k1},\dots,y_{kN})$ be the sequence at leaf $k$, $P_\pi(\rho)=\prod_l\pi_{\rho_l}$ and $P_{\rho y_k}(s_k)=\prod_lP_{\rho_ly_{kl}}(s_k)$. The maximum likelihood estimator $\hat\rho$ maximizes the likelihood jointly over the root sequence and the edge parameters (edge lengths profiled out). The empirical Bayes estimator $\hat\rho_B$ estimates the edge parameters first and then the ancestral states conditional on these estimates:

$$\hat s=\arg\max_s\sum_\rho P_\pi(\rho)\prod_kP_{\rho y_k}(s_k),\qquad \hat\rho_B=\arg\max_\rho P_\pi(\rho)\prod_kP_{\rho y_k}(\hat s_k).$$

**Theorem.** As $n\to\infty$ with $N$ fixed or slowly growing:

*(1)* The empirical Bayes estimator concentrates on the set $\mathcal H$ of maximizers of the limiting averaged likelihood: $\mathbb P(\hat\rho_B\in\mathcal H)\to1$. Both estimators are therefore consistent if $\mathcal H=\{\rho^*\}$ and inconsistent if $\rho^*\notin\mathcal H$; the case $\rho^*\in\mathcal H$ with $|\mathcal H|\ge2$ is not settled.

*(2)* (Symmetric models) If $\pi_1=\dots=\pi_c=1/c$, then $\mathbb P(\hat\rho=\rho^*)\to1$.

*(3)* (Inconsistency zone) If $\rho^*=(r,\dots,r)$, there exist $\pi$ and $\lim\bar s>0$ for which the MLE is inconsistent. A sufficient condition is $v(\pi_a)>v(\pi_r)$ for some state $a$, where, with $X\sim\mathrm{Bin}(N,p)$ and $\hat p=X/N$,

$$v(p)=\mathbb E\Big[\Big\{\hat p\log\frac{\hat p}{p}+(1-\hat p)\log\frac{1-\hat p}{1-p}\Big\}\mathbf 1\{\hat p>p\}\Big].$$

*(4)* (A consistent alternative) Let $\hat\pi_{jl}=\frac1n\sum_k\mathbf 1\{y_{kl}=j\}$ and $V(j,l)=\hat\pi_{jl}-\frac1{N-1}\sum_{v\ne l}\hat\pi_{jv}$, and set $\rho_l^{(D)}=\arg\max_jV(j,l)$. If $\liminf\bar s>0$, $N=O(\sqrt{n/\log n})$ and $\rho^*$ has at least two distinct states, then $\mathbb P(\rho^{(D)}=\rho^*)\to1$.

## Expansion

Under the proportional model $\mathbb E[\hat\pi_{jl}]=\pi_j-\pi_j\bar s+\mathbf 1\{\rho_l^*=j\}\bar s$, so the tip frequencies at each site are a mixture of the stationary distribution and a point mass at the ancestral state. The estimator $\rho^{(D)}$ subtracts the average frequency over the other sites to cancel the unknown $\bar s$. With unknown edge lengths, the profile likelihood instead lets each leaf choose its own $s_k$, and in the limit it compares Kullback–Leibler-type gains $v(\pi_j)$ across states. Under asymmetric $\pi$, a rare state can gain more from this per-leaf flexibility than the true common state, so the MLE can converge to the wrong ancestor even as the number of sequences grows. This contradicts the intuition that more taxa always help likelihood reconstruction.

## Sources

- Lam Si Tung Ho, Edward Susko, "Ancestral state reconstruction with large numbers of sequences and edge-length estimation", arXiv:2104.00151 (2021), Section 2 (star tree, proportional model, Assumption 1, Lemma 1), Section 3.2 (the two-step empirical Bayes estimator), Theorems 1–4, <https://doi.org/10.48550/arXiv.2104.00151>.

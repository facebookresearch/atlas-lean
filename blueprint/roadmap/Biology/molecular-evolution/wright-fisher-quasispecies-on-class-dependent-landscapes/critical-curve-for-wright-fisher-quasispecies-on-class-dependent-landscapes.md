# Critical curve for Wright–Fisher quasispecies on class-dependent landscapes

Genotypes are words of length $\ell$ over an alphabet of size $\kappa\ge2$. Each offspring mutates independently at every site with probability $q$, the new letter being uniform among the other $\kappa-1$. Fitness depends only on the Hamming class $k$ (distance to a master sequence): $A(0)>A(k)$ for all $k\ge1$, and there is $K\ge0$ with $A(K)\neq1$ and $A(k)=1$ for $k>K$ (the case $K=0$ is the sharp-peak landscape). A population of $m$ individuals evolves by the Wright–Fisher process: each generation, $m$ parents are drawn with replacement with probability proportional to fitness, and their offspring mutate. Let $\mu$ be the invariant probability measure of the occupancy process $(O_n(0),\dots,O_n(\ell))$ (numbers of individuals per class) and $\nu_k$ the image of $\mu$ under $o\mapsto(o(0),\dots,o(k))/m$. Consider the regime

$$ \ell\to\infty,\qquad m\to\infty,\qquad q\to0,\qquad \ell q\to a\in(0,\infty),\qquad m/\ell\to\alpha\in(0,\infty). $$

In this limit the mean dynamics of the first $K+1$ class proportions is the map $G_i(r)=\phi(r)^{-1}\sum_{h=0}^{i}r_hA(h)\,e^{-a}a^{i-h}/(i-h)!$, with mean fitness $\phi(r)=1+\sum_{h\le K}r_h(A(h)-1)$ (forward mutations become Poisson with mean $a$, with weights $e^{-a}a^j/j!$, and back mutations vanish). When $A(0)e^{-a}>1$, $G$ has a fixed point $\rho^0$ with $\rho^0_0>0$ whose basin is $\{r:r_0>0\}$; for the sharp peak, $\rho^0_0=(A(0)e^{-a}-1)/(A(0)-1)$.

**Theorem.** Let $\psi(a)=V(\rho^0,0)$, the large-deviation cost for the population to move from $\rho^0$ to the state with no individual in classes $0,\dots,K$, for $a<\ln A(0)$, and $\psi(a)=0$ for $a\ge\ln A(0)$. Then for every $k\ge0$:

- if $\alpha\psi(a)<\ln\kappa$, $\nu_k\to\delta_0$ weakly;
- if $\alpha\psi(a)>\ln\kappa$, $\nu_k\to\delta_{(\rho^0_0,\dots,\rho^0_k)}$ weakly.

Equivalently, the stationary mean proportion $\lim_n E[O_n(k)/m]$ tends to $0$ below the critical curve $\alpha\psi(a)=\ln\kappa$ and to $\rho^0_k$ above it, and its stationary variance tends to $0$ in both cases. The curve refines the deterministic error threshold $A(0)e^{-a}=1$: a quasispecies forms only if, in addition, the population is large enough that the time it persists near $\rho^0$, of order $e^{m\psi(a)}$, beats the time $\kappa^\ell$ needed to rediscover the master region by neutral drift.

## Depends on

- [Error threshold](../../population-dynamics/eigen-s-quasispecies-error-threshold/master-equilibrium-pos-iff.md)

## Expansion

Since $m\to\infty$ the multinomial transitions concentrate around $G$, and the occupancy process satisfies a large-deviation principle with cost $V_1$ for one-step transitions (Freidlin–Wentzell picture). Once the master region is lost the process is neutral and needs on the order of $\kappa^\ell$ generations to return; started from a single master sequence it reaches the basin of $\rho^0$ with non-negligible probability, and from there it stays near $\rho^0$ for a time of order $\exp(m\,V(\rho^0,0))$. Comparing $e^{m\psi(a)}=e^{\ell\alpha\psi(a)(1+o(1))}$ with $\kappa^\ell=e^{\ell\ln\kappa}$ and applying the ergodic theorem for the chain decides which regime dominates the invariant measure.

## Sources

- Joseba Dalmau, "The Wright–Fisher model for class–dependent fitness landscapes", *Electron. J. Probab.* 26 (2021), 1-44. <https://doi.org/10.1214/21-EJP704>
- Preprint version (the locators in this item follow its numbering): J. Dalmau, "The Wright–Fisher model for class–dependent fitness landscapes", arXiv:1712.00279 (2017), <https://doi.org/10.48550/arXiv.1712.00279>. Theorem 3.1 and Corollary 3.2 (dichotomy), Section 2 (the limiting map and its fixed points, Propositions 2.1 and 2.2), Section 10 (definition of $\psi$). The sharp-peak value of $\rho^0_0$ is obtained by solving $G_0(r)=r_0$ with $K=0$. The preprint's display of the limiting map omits the Poisson factor $e^{-a}$; the published version (eq. (2.8)) includes it, and the map above follows the published version.

# Variance of coupled tau-leaping paths and multilevel Monte Carlo complexity

**Setting.** A stochastic reaction network with $d$ species and $K$ reactions, reaction vectors $\zeta_k$, is scaled by a system-size parameter $N$: species are normalized as $X_i^N=N^{-\alpha_i}X_i$, reaction vectors become $\zeta_k^N=O(N^{-\rho_k})$, raw intensities are written $\lambda_k=N^{r_k}\lambda_k^N$ with $\lambda_k^N=O(1)$, and $\rho=\min_k\rho_k$, $\gamma=\max_k(r_k-\rho_k)$ (the natural time scale), $c_k=r_k-\gamma\le\rho_k$. The exact process and the tau-leaping approximation with step $h$ are

$$X^N(t)=X^N(0)+\sum_kY_k\Big(N^{\gamma}\!\int_0^tN^{c_k}\lambda_k^N(X^N(s))\,ds\Big)\zeta_k^N,$$

$$Z_h^N(t)=Z_h^N(0)+\sum_kY_k\Big(N^{\gamma}\!\int_0^tN^{c_k}\lambda_k^N\big(Z_h^N(\lfloor s/h\rfloor h)\big)\,ds\Big)\zeta_k^N,$$

with $Y_k$ independent unit-rate Poisson processes. The classical scaling is $c_k=\rho_k=1$, $\gamma=0$. Pairs $(X^N,Z_h^N)$ and successive tau-leap levels $(Z^N_\ell,Z^N_{\ell-1})$, $h_\ell=TM^{-\ell}$, are coupled by the split-Poisson construction: a shared process runs at the minimum of the two intensities and independent processes run at the excesses.

**Running assumption.** There is $C>0$ with $\sum_k|\lambda_k^N|$, $\sum_k|\partial_j\lambda_k^N|$ and $\sum_k|\partial_i\partial_l\lambda_k^N|$ all bounded by $C$.

**Theorem.** Let $f:\mathbb R^d\to\mathbb R$ be $C^2$ with first and second partial derivatives bounded by $M$. Under the running assumption and the coupling, for $0\le t\le T$,

$$\operatorname{Var}\big(f(X^N(t))-f(Z_h^N(t))\big)\le\bar C_1(N^{\gamma}T,d,M)\,N^{-\rho}(N^{\gamma}h)^2+\bar C_2(N^{\gamma}T,d,M)\,N^{-\rho}(N^{\gamma}h),$$

and the same form of bound, with constants $\bar D_1,\bar D_2$, holds for $\operatorname{Var}\big(f(Z^N_\ell(t))-f(Z^N_{\ell-1}(t))\big)$ with $h=h_\ell$. The constants depend on $N$ and $T$ only through $N^\gamma T$, so for fixed $T$ and $\gamma\le0$ they are bounded uniformly in $N$.

**Complexity consequence.** If $\gamma\le0$ and $\bar C_1$ is not much larger than $\bar C_2$, level variances are of order $N^{-\rho}N^{\gamma}h_\ell$. Choosing $n_\ell\propto N^{-\rho}N^{\gamma}(L+1)h_\ell\epsilon^{-2}$ samples per level, coarsest level $\ell_0=0$ and $h_L=O(\epsilon)$ ($L=O(|\ln\epsilon|)$ levels), the biased multilevel tau-leaping estimator of $\mathbb E f(X^N(T))$ reaches root-mean-square error $\epsilon$ at cost of order

$$N^{-\rho}N^{\gamma}\,\epsilon^{-2}\,(\ln\epsilon)^2 .$$

The unbiased variant, which adds a coupled exact-versus-finest-level correction, costs $N^{-\rho}N^{\gamma}\epsilon^{-2}(\ln\epsilon)^2+\max\{N^{-\rho}N^{\gamma}|\ln\epsilon|\,h_L\epsilon^{-2},1\}\cdot\bar N$, where $\bar N=N^{\gamma}\sum_kN^{c_k}$ is the cost of one exact path.

## Expansion

Earlier analysis bounded the variance by the $L^2$ distance between coupled paths, giving $\bar C_{11}(N^\gamma h)^2+\bar C_{22}N^{-\rho}N^\gamma h$; the $h^2$ term, not multiplied by $N^{-\rho}$, usually dominated (for instance under the classical scaling with $h>N^{-1}$) and added a term of order $\max\{N^{2\gamma}h_L^2\epsilon^{-2},1\}\cdot\bar N$ to the complexity. The new bound works with the variance directly: write $f(X^N)-f(Z^N_h)$ via the centered Poisson martingales and the drift $F^N=\sum_kN^{\gamma+c_k}\lambda_k^N\zeta_k^N$, compare both processes with the deterministic ODE $\dot x^N=F^N(x^N)$, and use that every fluctuation term carries a factor $N^{-\rho}$ from the jump size. Second-order Taylor control of $f$ and Gronwall bounds with Lipschitz constant $\sqrt d\,CN^\gamma$ give constants depending on $N^\gamma T$. The level-wise variance budget then reduces to the standard multilevel Monte Carlo cost calculation, and with variances proportional to $h_\ell$ the optimal coarsest level is $\ell_0=0$.

These are Theorem 1 and Corollary 1 of the source and the complexity bounds of its section on consequences for complexity.

## Sources

- D. F. Anderson, D. J. Higham, Y. Sun, *Complexity of Multilevel Monte Carlo Tau-Leaping*, SIAM J. Numer. Anal. 52 (2014); arXiv:1310.2676. <https://doi.org/10.48550/arXiv.1310.2676>

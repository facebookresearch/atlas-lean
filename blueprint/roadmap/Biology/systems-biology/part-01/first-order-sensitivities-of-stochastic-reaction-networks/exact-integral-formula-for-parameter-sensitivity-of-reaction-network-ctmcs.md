# Exact integral formula for parameter sensitivity of reaction-network Markov chains

**Setting.** A stochastic reaction network with $d$ species and $K$ reactions is a continuous-time Markov chain $X_\theta$ on $\mathbb N_0^d$ that jumps by $\zeta_k$ at rate $\lambda_k(x,\theta)$, with total rate $\lambda_0(x,\theta)=\sum_k\lambda_k(x,\theta)$. For an output $f$ and horizon $T$, let $\Psi_\theta(x,f,t)=\mathbb E[f(X_\theta(t))\mid X_\theta(0)=x]$ and define the sensitivity $S_\theta(f,T)=\partial_\theta\Psi_\theta(x_0,f,T)$. Write $\Delta_{\zeta}f(x)=f(x+\zeta)-f(x)$ and

$$
R_\theta(x,f,t,k)=\int_0^t\Big(\Psi_\theta(x+\zeta_k,f,s)-\Psi_\theta(x,f,s)-\Delta_{\zeta_k}f(x)\Big)e^{-\lambda_0(x,\theta)(t-s)}\,ds.
$$

**Assumptions.** $|f(x)|\le C(1+\|x\|^r)$; each $\lambda_k(x,\cdot)$ is $C^2$ near $\theta$, with $\lambda_k$, $\partial_\theta\lambda_k$ and a local supremum of $\partial^2_\theta\lambda_k$ of polynomial growth; reactions cannot drive counts negative; and the total rate of population-increasing reactions grows at most linearly, $\sum_{k:\langle\mathbf 1,\zeta_k\rangle>0}\lambda_k(x,\theta)\le C_\lambda(1+\|x\|)$.

**Theorem.** Under these assumptions $S_\theta(f,T)$ is well defined and $S_\theta(f,T)=\mathbb E[s_\theta(f,T)]$, where, with $\sigma_0=0<\sigma_1<\cdots$ the jump times of $X_\theta$,

$$
s_\theta(f,T)=\sum_{k=1}^K\Bigg(\int_0^T\frac{\partial\lambda_k(X_\theta(t),\theta)}{\partial\theta}\,\Delta_{\zeta_k}f(X_\theta(t))\,dt+\sum_{i\ge0:\,\sigma_i<T}\frac{\partial\lambda_k(X_\theta(\sigma_i),\theta)}{\partial\theta}\,R_\theta\big(X_\theta(\sigma_i),f,T-\sigma_i,k\big)\Bigg).
$$

## Expansion

Using Kurtz's random time-change representation, the processes at $\theta$ and $\theta+h$ are coupled through shared unit-rate Poisson processes; to first order in $h$ they differ only when an extra firing of some reaction $k$ occurs, at rate $h\,\partial_\theta\lambda_k$. The first term accounts for the immediate effect $\Delta_{\zeta_k}f$ of such an extra firing, and $R_\theta$ accounts for the subsequent divergence of the perturbed trajectory, discounted by the probability that the unperturbed chain has not yet jumped from state $x$. Each $R_\theta$ is estimated by short auxiliary simulations, giving an unbiased estimator. Unlike the likelihood-ratio (Girsanov) estimator, its variance does not blow up when the sensitive rate constant is small, and it can even give the sensitivity to a reaction whose rate is set to zero.

## Sources

- Ankit Gupta, Mustafa Khammash, "Unbiased estimation of parameter sensitivities for stochastic chemical reaction networks", arXiv:1210.3475: Section 2: Conditions 2.1–2.2 and Theorem 2.3 (main result), Examples 2.4–2.5; Section 3 (estimation algorithm); Section 4 (proof, Lemma 4.1). <https://doi.org/10.48550/arXiv.1210.3475>

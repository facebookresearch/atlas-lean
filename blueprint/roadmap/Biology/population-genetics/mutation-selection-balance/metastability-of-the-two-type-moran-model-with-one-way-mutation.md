# Metastability of the two-type Moran model with one-way mutation

Fix a population size $N$, a mutation rate $m_N>0$ and a selection parameter $s_N>0$. Let $Y_0=Y_0^{(N)}$ be the number of type-$0$ individuals in a two-type Moran model where type $0$ mutates to type $1$ at rate $m_N$ per individual (no back mutation) and type $0$ has selective advantage $s_N/N$ per encounter against type $1$. It is a birth-death chain on $\{0,\dots,N\}$ with up-rates $\lambda_n=(\tfrac1{2N}+\tfrac{s_N}N)n(N-n)$ and down-rates $\mu_n=\tfrac1{2N}n(N-n)+m_Nn$, and its drift is

$$\lambda_n-\mu_n=n(s_N-m_N)\Bigl(1-\frac n{\mathfrak a_N}\Bigr),\qquad\mathfrak a_N=N(1-\rho_N),\quad\rho_N=\frac{m_N}{s_N}.$$

Define the critical size $\mathfrak c_N=1/(s_N-m_N)$, $\mathfrak u_N=\rho_N\mathfrak a_N/\mathfrak c_N=Nm_N(1-\rho_N)^2$, the fluctuation scale $\sigma_N=\mathfrak c_N\sqrt{\mathfrak u_N}=s_N^{-1}\sqrt{Nm_N}$, and

$$e_N=\mathfrak c_N\sqrt{\frac\pi{\mathfrak u_N}}\exp\bigl(2\mathfrak u_N\eta(m_N,\rho_N)\bigr),\quad \eta(m,\rho)=-\frac1{2m}\Bigl[\frac{1}{1-\rho}\log\frac{1+2m}{1+2m/\rho}+\sum_{\ell\ge1}\Bigl(1-\frac1{(1+2m)^\ell}\Bigr)\frac{(1-\rho)^{\ell-1}}{\ell(\ell+1)}\Bigr].$$

Assume, as $N\to\infty$, the moderate-mutation regime $1/N\ll m_N<s_N\ll1$ with $\rho_N\to\rho^*\in(0,1]$, and the exponential regime $\mathfrak u_N\to\infty$ (equivalently $\mathfrak c_N\ll\mathfrak a_N$).

**Theorem.** Let $T_\ell$ be the hitting time of $\ell$ and $T_0$ the extinction time of $Y_0$.

1. The times to come down from $N$ to $\lfloor\mathfrak a_N\rfloor$, to climb from $1$ to $\lfloor\mathfrak a_N\rfloor$ conditioned on avoiding $0$, and to fall from $\lfloor\mathfrak a_N\rfloor-1$ to $0$ conditioned on avoiding $\lfloor\mathfrak a_N\rfloor$, all have expectations $O(\mathfrak c_N\log\mathfrak a_N)$.
2. Started at $\lfloor\mathfrak a_N\rfloor$, the rescaled process $\bigl(\sigma_N^{-1}(Y_0(t\mathfrak c_N)-\mathfrak a_N)\bigr)_{t\ge0}$ converges in distribution to the standard Ornstein-Uhlenbeck process $d\mathcal H=-\mathcal H\,dt+d\mathcal W$, $\mathcal H(0)=0$.
3. The quasi-equilibrium $\alpha_N$ of $Y_0$ (the law on $\{1,\dots,N\}$ invariant under conditioning on non-extinction) is asymptotically normal: its image under $n\mapsto(n-\mathfrak a_N)/\sigma_N$ converges weakly to $\mathcal N(0,1/2)$.
4. Started from $j_N\gg\mathfrak c_N$, $T_0/e_N$ converges in distribution to a standard exponential random variable; in particular $\mathbb E[T_0]\sim e_N$.
5. For $\varepsilon<1/3$, with high probability the type-$0$ population experiences $\gg\mathfrak c_N$ mutations between its last visit to $\lfloor2\varepsilon\mathfrak a_N\rfloor$ and its extinction.

## Expansion

The process lives in a potential well $U^{(N)}$ centered at $\mathfrak a_N$ that is quadratic on the scale $\sigma_N$, $U(\mathfrak a+K\sigma)-U(\mathfrak a)=K^2(1+o(1))$, which gives the Gaussian quasi-equilibrium and the Ornstein-Uhlenbeck limit. The well depth is $2\mathfrak u_N\eta$, so escape to $0$ requires an exponentially rare excursion, while relaxation within the well takes only $O(\mathfrak c_N\log\mathfrak a_N)$; this separation of time scales yields the exponential limit of the extinction time. Part 5 uses a time-reversal identity for the final excursion.

## Sources

- J. L. Igelbrink, C. Smadi and A. Wakolbinger, "The tournament ratchet's clicktime process, and metastability in a Moran model", arXiv preprint (2025), <https://doi.org/10.48550/arXiv.2512.24779>. Section 2 (Remark 2.2, the drift, $\mathfrak a$, $\mathfrak c$, $\mathfrak u$, $\sigma$, $e_N$, $\eta$ and the regime assumptions), Theorem 2.4, Proposition 3.1, Lemmas 3.3, 3.5, 3.8 and 3.11, and Propositions 3.10 and 3.14 (Section 3, proof of Theorem 2.4).

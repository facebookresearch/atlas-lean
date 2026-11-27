# Persistence threshold of the distributed-delay SIR model with Lévy jumps

**Setting.** In the SIR model with recruitment $A>0$, natural death rates $\mu_1,\mu_2>0$, recovery rate $\gamma>0$ and transmission $\beta>0$, infection is driven by the delayed force $\mathcal D(t)=\int_{-\infty}^t\eta e^{-\eta(t-s)}I(s)\,ds$ (a Gamma, here exponential, memory kernel with fading rate $\eta>0$). The linear chain trick turns the deterministic delay model into an ODE whose threshold is

$$\mathcal T^\star=\frac{\beta A}{\mu_1(\mu_2+\gamma)}.$$

Perturbing each equation by Brownian noise $\sigma_iX\,dW_i$ and compensated Poisson jumps $\int_{\mathcal U}\lambda_i(u)X(t^-)\,\widetilde N(dt,du)$ (independent Brownian motions $W_i$, Poisson random measure with finite characteristic measure $\nu$ on $\mathcal U\subset(0,\infty)$) gives

$$dS=(A-\mu_1S-\beta S\mathcal D)\,dt+\sigma_1S\,dW_1+\int_{\mathcal U}\lambda_1(u)S(t^-)\widetilde N(dt,du),$$

$$dI=(\beta S\mathcal D-(\mu_2+\gamma)I)\,dt+\sigma_2I\,dW_2+\int_{\mathcal U}\lambda_2(u)I(t^-)\widetilde N(dt,du),$$

$$d\mathcal D=\eta(I-\mathcal D)\,dt+\sigma_4\mathcal D\,dW_4+\int_{\mathcal U}\lambda_4(u)\mathcal D(t^-)\widetilde N(dt,du).$$

Assume $(\mathcal H_1)$: $\int_{\mathcal U}\lambda_i^2\,d\nu<\infty$, and $(\mathcal H_2)$: $1+\lambda_i>0$ and $\int_{\mathcal U}(\lambda_i-\ln(1+\lambda_i))\,d\nu<\infty$, for $i=1,2,4$, and write

$$\bar\sigma_i=\tfrac12\sigma_i^2+\int_{\mathcal U}\big(\lambda_i(u)-\ln(1+\lambda_i(u))\big)\,\nu(du).$$

For items 2 and 3 the source also assumes, with $\bar\sigma:=\max\{\sigma_1^2,\sigma_2^2,\sigma_4^2\}$, $\vartheta:=\min\{\mu_1,\mu_2+\gamma-\eta,\eta\}$, $\bar\lambda(u):=\max_i\lambda_i(u)$, $\underline\lambda(u):=\min_i\lambda_i(u)$ ($i=1,2,4$), $\hat\zeta_p:=(1+\bar\lambda)^p-1-p\bar\lambda$, $\check\zeta_p:=(1+\underline\lambda)^p-1-p\underline\lambda$ and $\ell_p:=\int_{\mathcal U}\max\{\hat\zeta_p,\check\zeta_p\}\,d\nu$:

- $(\mathcal H_3)$: $\int_{\mathcal U}\big[\ln(1+\lambda_i(u))\big]^2\nu(du)<\infty$ for $i=1,2,4$;
- $(\mathcal H_4)$: $\int_{\mathcal U}\big[(1+\bar\lambda(u))^2-1\big]^2\nu(du)<\infty$;
- $(\mathcal H_5)$: there is $p>2$ with $\chi_{1,p}:=\vartheta-\frac{p-1}2\bar\sigma-\frac1p\ell_p>0$.

**Theorem.**
1. (Well-posedness) Under $(\mathcal H_1)$–$(\mathcal H_2)$, for every initial value in $\mathbb R^3_+$ there is a unique global solution, which stays in $\mathbb R^3_+$ almost surely.
2. (Persistence in the mean) Assume $(\mathcal H_1)$–$(\mathcal H_5)$, and let

$$\widetilde{\mathcal T}^\star=\beta\,\frac{A}{\mu_1+\bar\sigma_1}\Big((\mu_2+\gamma+\bar\sigma_2)+\beta\,\frac{A}{\mu_1+\bar\sigma_1}\,\frac{\bar\sigma_4}{\eta}\Big)^{-1}.$$

If $\widetilde{\mathcal T}^\star>1$, then $\liminf_{t\to\infty}\frac1t\int_0^tI(s)\,ds>0$ almost surely.
3. (Exponential extinction) Assume $(\mathcal H_1)$–$(\mathcal H_5)$. Let $\Upsilon:=\min\{\mu_2+\gamma,\eta\}(\sqrt{\mathcal T^\star}-1)$ if $\mathcal T^\star\le1$ and $\Upsilon:=\max\{\mu_2+\gamma,\eta\}(\sqrt{\mathcal T^\star}-1)$ if $\mathcal T^\star>1$; $\Lambda:=\sigma_1^2+\int_{\mathcal U}\lambda_1^2\,d\nu$; $\chi_2:=2\mu_1-\sigma_1^2-\int_{\mathcal U}\lambda_1^2\,d\nu$ (positive under $(\mathcal H_4)$–$(\mathcal H_5)$); $\Sigma:=\big(2(\sigma_2^{-2}+\sigma_4^{-2})\big)^{-1}$; $\Pi:=\int_{\mathcal U}\aleph\,d\nu$ with $\aleph(u):=\big[\ln(1+m(u))-m(u)\big]\mathbf 1_{\{m(u)>0\}}+\big[\ln(1+M(u))-M(u)\big]\mathbf 1_{\{M(u)\le0\}}$, $m=\lambda_2\wedge\lambda_4$, $M=\lambda_2\vee\lambda_4$; and

$$\Theta:=\Upsilon+\Pi-\Sigma+\eta\Big(\frac{\mathcal T^\star\Lambda}{\chi_2}\Big)^{1/2}.$$

Then

$$\limsup_{t\to\infty}\frac1t\ln\Big(\frac{I(t)}{\mu_2+\gamma}+\frac{\sqrt{\mathcal T^\star}}{\eta}\mathcal D(t)\Big)\le\Theta\quad\text{a.s.};$$

if $\Theta<0$, then $I(t)\to0$ and $\mathcal D(t)\to0$ exponentially fast almost surely.

With no noise ($\bar\sigma_i=0$), $\widetilde{\mathcal T}^\star$ reduces to $\mathcal T^\star$: noise and jumps raise the effective death and removal rates by $\bar\sigma_i$ and so make persistence harder.

## Expansion

Global positivity uses a logarithmic Lyapunov function and a stopping-time argument; hypothesis $1+\lambda_i>0$ keeps jumps from crossing zero. For persistence, apply Itô's formula with jumps to $\ln I$ and $\ln\mathcal D$ with weights chosen from the linear chain: the jump terms contribute exactly $-\bar\sigma_i$ to the drift, and comparing $S$ with the solution $\psi$ of the disease-free stochastic logistic-type equation $d\psi=(A-\mu_1\psi)dt+\dots$, whose time averages satisfy $\frac1t\int_0^t\psi\to A/\mu_1$, gives a lower bound on $\frac1t\int_0^tI$ that is positive exactly when $\widetilde{\mathcal T}^\star>1$. Extinction combines the same comparison with the strong law for local martingales and the second-moment averages of $\psi$.

## Sources

- Driss Kiouach, Yassine Sabbar, "The long-time behaviour of a stochastic SIR epidemic model with distributed delay and multidimensional Lévy jumps", arXiv:2003.08219 (2020), systems (1.1)–(2.1), hypotheses $(\mathcal H_1)$–$(\mathcal H_5)$, Theorem 2.1, Lemmas 3.1 and 3.4, Theorem 3.7 (extinction) and Theorem 3.10 (persistence in the mean), <https://doi.org/10.48550/arXiv.2003.08219>.

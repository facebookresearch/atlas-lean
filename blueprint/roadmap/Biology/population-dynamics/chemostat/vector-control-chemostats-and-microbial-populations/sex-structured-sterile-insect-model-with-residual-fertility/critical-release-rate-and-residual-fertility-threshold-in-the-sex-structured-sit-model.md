# Critical release rate and residual-fertility threshold in the sex-structured SIT model

**Model.** Wild males $M$ and females $F$ compete with sterile males $M_S$, a fraction $\epsilon\in[0,1)$ of which remain fertile (residual fertility). With sex ratio $r$, viable egg production $\rho$, death rates $\mu_M,\mu_F,\mu_S$ (with $\mu_S\ge\mu_M$), competition parameter $\beta>0$ and sterile-male competitiveness $\gamma\in(0,1]$,

$$
\begin{aligned}
\dot M&=r\rho\,\frac{F(M+\epsilon\gamma M_S)}{M+\gamma M_S}\,e^{-\beta(M+F)}-\mu_MM,\\
\dot F&=(1-r)\rho\,\frac{F(M+\epsilon\gamma M_S)}{M+\gamma M_S}\,e^{-\beta(M+F)}-\mu_FF,\\
\dot M_S&=\Lambda-\mu_SM_S .
\end{aligned}
$$

Define the basic offspring numbers $\mathcal N_F=(1-r)\rho/\mu_F$ and $\mathcal N_M=r\rho/\mu_M$, both assumed $>1$. Without releases the population converges to the wild equilibrium $(M_w^*,F_w^*)=\frac{\ln\mathcal N_F}{\beta(\mathcal N_F+\mathcal N_M)}(\mathcal N_M,\mathcal N_F)$.

**Constant releases.** Fix $M_S\equiv M_S^*=\Lambda/\mu_S$. Positive equilibria satisfy $F^*/M^*=\mathcal N_F/\mathcal N_M$.

1. If $\epsilon<\mathcal N_F^{-1}$, there is $\Lambda^\epsilon_{\rm crit}>0$ such that the system has two positive equilibria for $0<\Lambda<\Lambda^\epsilon_{\rm crit}$, one for $\Lambda=\Lambda^\epsilon_{\rm crit}$ and none for $\Lambda>\Lambda^\epsilon_{\rm crit}$, where

$$
\Lambda^\epsilon_{\rm crit}=\frac{2}{1-\epsilon}\,\frac{\mu_S}{\beta\gamma(1+\mathcal N_F/\mathcal N_M)}\,\Phi_\epsilon
$$

and $\Phi_\epsilon$ is the unique positive solution of

$$
1+\Phi\Big(1+\sqrt{1+2/\Phi}\Big)=\mathcal N_F\,e^{-2\frac{\epsilon}{1-\epsilon}\Phi}\,e^{-2/(1+\sqrt{1+2/\Phi})} .
$$

2. If $\mathcal N_F^{-1}<\epsilon<1$, then for every $\Lambda>0$ there is a positive equilibrium bounded below componentwise by $\frac{\ln(\epsilon\mathcal N_F)}{\beta(\mathcal N_F+\mathcal N_M)}(\mathcal N_M,\mathcal N_F)$: no release size eliminates the population.

The extinction equilibrium $\mathbf 0$ is locally asymptotically stable if $\epsilon<\mathcal N_F^{-1}$ and unstable if $\epsilon>\mathcal N_F^{-1}$ (at $\epsilon=\mathcal N_F^{-1}$ the Jacobian has eigenvalues $-\mu_M$ and $0$, and the higher-order terms on the centre manifold decide; for large releases they make $\mathbf 0$ attract nearby states in $\mathbb R_+^2$); for $\Lambda>\Lambda^\epsilon_{\rm crit}$ it is globally asymptotically stable, while for $0<\Lambda<\Lambda^\epsilon_{\rm crit}$ the system is bistable, the order interval $[\mathbf 0,\mathbf E_1^*)$ below the smaller positive equilibrium lying in the basin of $\mathbf 0$.

**Periodic impulsive releases.** If a quantity $\tau\Lambda$ is released every $\tau$ days, $M_S$ approaches the $\tau$-periodic profile $M_{s,\rm per}(t)=\frac{\tau\Lambda}{1-e^{-\mu_S\tau}}e^{-\mu_S(t-\lfloor t/\tau\rfloor\tau)}$. If $\epsilon<\mathcal N_F^{-1}$ and

$$
\Lambda>\Lambda^{\rm per}_{\rm crit}=\frac{2(\cosh(\mu_S\tau)-1)}{\mu_S\tau^2}\,\frac{(1-\epsilon)\mathcal N_F}{\gamma(1-\epsilon\mathcal N_F)\,e\beta},
$$

then every solution of the periodically forced system converges to $\mathbf 0$.

## Expansion

At equilibrium the female equation gives $\mathcal N_Fe^{-cM}=1+(1-\epsilon)\frac{a}{M+\epsilon a}$ with $a=\gamma M_S^*$ and $c=\beta(1+\mathcal N_F/\mathcal N_M)$. The right side at $M=0$ equals $1/\epsilon$, so the sign of $1/\epsilon-\mathcal N_F$ decides whether arbitrarily large releases can push the left side below the right everywhere; the double-root condition $f=f'=0$ yields $\Phi_\epsilon$ and hence $\Lambda^\epsilon_{\rm crit}$. The Jacobian at $\mathbf 0$ has eigenvalues $-\mu_M$ and $(1-r)\rho\epsilon-\mu_F$, and a Dulac function $\frac{M+\gamma M_S^*}{F(M+\epsilon\gamma M_S^*)}$ rules out periodic orbits, giving global stability when $\mathbf 0$ is the only equilibrium. For periodic releases, $xe^{-\beta x}\le 1/(e\beta)$ bounds the per-capita female growth by $(1-r)\rho\big((1-\epsilon)/(e\beta\gamma M_{s,\rm per})+\epsilon\big)-\mu_F$; integrating over one period with $\langle 1/M_{s,\rm per}\rangle=2(\cosh(\mu_S\tau)-1)/(\mu_S\tau^2\Lambda)$ makes $F(n\tau)$ decrease geometrically.

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- M. S. Aronna, Y. Dumont, "On nonlinear pest/vector control via the Sterile Insect Technique: impact of residual fertility", arXiv:2005.05595 (2020), Section 2 (continuous SIT model, Proposition 2 and the asymptotic analysis of equilibria) and Section 3 (impulsive periodic releases, Theorem 1), <https://doi.org/10.48550/arXiv.2005.05595>.

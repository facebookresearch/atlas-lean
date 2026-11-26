# Recurrence-time asymptotics and parameter estimation under therapy

**Model.** A tumor of $n$ cells at treatment start consists of drug-sensitive cells and $n^\beta$ pre-existing resistant cells, $\beta\in(0,1)$. Sensitive cells have birth and death rates $r_0,d_0$ with net rate $\lambda_0=r_0-d_0<0$ under treatment, and each sensitive cell produces a resistant mutant at rate $n^{-\alpha}$, $\alpha\in(0,1)$. Resistant cells die at rate $d_1$ and give birth at a density-dependent rate $f(\cdot)$ of the scaled total population (carrying capacity $K$), bounded below by $\lambda_1(1-(x+y))+d_1$ and vanishing at infinity; generalized logistic $f(x,y)=\lambda_1(1-(x+y)^\nu)+d_1$, $\nu\ge1$, qualifies. With $\phi=f-d_1$, the scaled sensitive, resistant and initial-clone populations $X_0,X_1,X_\beta$ are approximated by

$$\dot y_0=\lambda_0y_0,\qquad \dot y_1=\phi(y)\,y_1+n^{-\alpha}y_0,\qquad \dot y_\beta=\phi(y)\,y_\beta,$$

started at $(n/K,n^\beta/K,n^\beta/K)$. The deterministic recurrence time is $\zeta_n=\inf\{t>0:y_1(t)=n/K\}$, the first time the resistant population regains the initial tumor size.

**Proposition 1.** $\displaystyle\lim_{n\to\infty}\frac{\zeta_n}{\log n}=\frac{\min\{1-\beta,\alpha\}}{\lambda_1}.$

**Theorem 1 (functional law of large numbers up to recurrence).** If $\beta>1+\lambda_1/\lambda_0$ and $\alpha+\beta>1$, then for any $\epsilon,\delta>0$, $u_1<\beta/2$ and $u_2<\min\{\beta/2,\alpha+\beta-1\}$,

$$\sup_{t\le\zeta_n+\delta}\Big|\frac{X_0}{y_0}-1\Big|\to0,\qquad n^{u_1}\sup_{t\le\zeta_n+\delta}\Big|\frac{X_1}{y_1}-1\Big|\to0,\qquad n^{u_2}\sup_{t\le\zeta_n+\delta}\Big|\frac{X_\beta}{y_\beta}-1\Big|\to0$$

in probability. The first condition keeps sensitive cells present at recurrence; the second makes the pre-existing clone dominate the mutant-derived resistant cells.

**Theorem 2.** Under the same conditions, estimators $\hat\alpha,\hat\beta,\hat\lambda_0,\hat\lambda_1$ built from the stochastic recurrence time, the sizes of the sensitive and resistant populations, and the size of the largest resistant clone at recurrence are consistent.

## Expansion

While resistant cells are far below capacity, $\phi\approx\lambda_1$ and the resistant population grows like $n^\beta e^{\lambda_1t}$ from pre-existing cells plus $\int_0^tn^{1-\alpha}e^{\lambda_0s}e^{\lambda_1(t-s)}ds\asymp n^{1-\alpha}e^{\lambda_1t}$ from mutants, so it reaches order $n$ after time $\approx\log n\cdot\min\{1-\beta,\alpha\}/\lambda_1$. Since $\lambda_0<0$, the sensitive population at that time is $n^{1+\lambda_0\min\{1-\beta,\alpha\}/\lambda_1}$, which still diverges when $\beta>1+\lambda_1/\lambda_0$ (Proposition 2 gives the order of the initial clone). The stochastic processes are compared with the ODE on a growing time horizon by martingale estimates for the Poisson-driven SDEs, with errors relative to the deterministic sizes decaying polynomially in $n$. Inverting the deterministic asymptotics for $\zeta_n$, the clone-size exponents and the residual sensitive fraction gives the estimators.

## Sources

- K. Leder, Z. Wang, X. Zhang, "Parameter Estimation in Recurrent Tumor Evolution with Finite Carrying Capacity", arXiv preprint (2025), Propositions 1–2, Theorem 1 and Theorem 2, <https://doi.org/10.48550/arXiv.2510.01078>.

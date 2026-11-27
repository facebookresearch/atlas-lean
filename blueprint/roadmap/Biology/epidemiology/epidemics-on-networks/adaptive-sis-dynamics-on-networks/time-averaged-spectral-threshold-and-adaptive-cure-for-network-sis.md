# Time-averaged spectral threshold and adaptive cure control for SIS dynamics on networks

**Model.** Nodes $v=1,\dots,n$ of a (possibly time-varying) directed contact graph with adjacency matrix $A(t)=(a_{vu}(t))$ are susceptible or infectious; $i_v(t)$ is the probability that $v$ is infectious. Each infectious neighbor infects $v$ with rate (probability per unit time) $\gamma(t)$ and $v$ is cured at rate $\beta_v(t)$, both allowed to vary in time (adaptive attack and defense). In the individual-based mean-field (independence) approximation,

$$\frac{di_v}{dt}=\Bigl[1-\prod_{u}\bigl(1-\gamma(t)\,a_{vu}(t)\,i_u(t)\bigr)\Bigr]\bigl(1-i_v(t)\bigr)-\beta_v(t)\,i_v(t),$$

which is dominated by the linear comparison system $\dot x=(\gamma(t)A(t)-\operatorname{diag}\beta_v(t))\,x$.

**Theorem (semi-adaptive defense).** Suppose all nodes share the cure rate $\beta(t)$ and the topology is fixed, with largest-modulus eigenvalue $\lambda_1$ of $A$. Suppose the time averages

$$\bar\gamma=\lim_{t\to\infty}\frac1t\int_{t_0}^{t_0+t}\gamma(s)\,ds,\qquad \bar\beta=\lim_{t\to\infty}\frac1t\int_{t_0}^{t_0+t}\beta(s)\,ds$$

exist uniformly in $t_0$. If $\lambda_1<\bar\beta/\bar\gamma$, the infection dies out from every initial configuration; if $\lambda_1>\bar\beta/\bar\gamma$, it does not die out from some initial configurations. If $\beta(t)$ and $\gamma(t)$ are ergodic stationary processes whose time averages converge uniformly almost surely, the same dichotomy holds almost surely with $\bar\beta,\bar\gamma$ replaced by their stationary means $\mathbb E\beta(0)$, $\mathbb E\gamma(0)$.

**Theorem (fully adaptive defense).** If each node raises its cure rate in proportion to its own infection level, starting from $\beta_v(0)=0$,

$$\frac{d\beta_v}{dt}=\rho\,i_v(t),\qquad\rho>0,$$

then the infection dies out from every initial configuration, and the cumulative infection is bounded:

$$\int_0^\infty\sum_{v=1}^ni_v(s)\,ds\le\frac{(n-1)^2\gamma_m}{\rho}+\frac{n-1}{\rho}\sqrt{\sum_{v=1}^ni_v(0)+\frac{(n-1)^3\gamma_m^2}{2\rho}},\qquad\gamma_m=\sup_t\gamma(t).$$

A modified adaptive law can also steer the infection to a prescribed endemic level instead of zero.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../../sis-extinction-times-on-finite-graphs/prob-ne-empty-le.md)

## Expansion

Since $1-\prod_u(1-\gamma a_{vu}i_u)\le\gamma\sum_ua_{vu}i_u$ and $1-i_v\le1$, the nonlinear system is bounded above by the linear time-varying comparison system, so die-out of the latter implies die-out of the former. With a common cure rate and fixed topology the comparison system is $\dot x=(\gamma(t)A-\beta(t)I)x$, whose solution is $x(t)=\exp\bigl(A\int_0^t\gamma-I\int_0^t\beta\bigr)x(0)$ because the two matrices commute; it decays iff $\lambda_1\int_0^t\gamma-\int_0^t\beta\to-\infty$, i.e. iff $\lambda_1\bar\gamma<\bar\beta$, and the reverse inequality makes the Perron component grow, which near zero transfers to the nonlinear system. For the adaptive law, $\beta_v$ is non-decreasing and $\rho\int_0^\infty i_v=\beta_v(\infty)$; a Lyapunov-type estimate shows that the cure rates stay bounded, so $i_v$ is integrable, and uniform continuity then forces $i_v(t)\to0$ (Barbalat's lemma).

## Sources

- Shouhuai Xu, Wenlian Lu, Li Xu, Zhenxin Zhan, "Adaptive Epidemic Dynamics in Networks: Thresholds and Control", arXiv (2013). Section 2 (model, master equation (2); Theorem 1, Theorem 2 and Corollary 1 for semi-adaptive defense; Theorem 3, Proposition 1, Theorem 4 and Proposition 2 for fully adaptive defense). <https://doi.org/10.48550/arXiv.1311.2180>. Published version: ACM Transactions on Autonomous and Adaptive Systems 8(4) (2014), 1–19, <https://doi.org/10.1145/2555613>; locators above refer to the arXiv version.

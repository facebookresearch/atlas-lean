# Global stability of the SAIRP model and pseudo-oscillations under switching policies

**Model (SAIRP).** The population is split into susceptible $S$, asymptomatic infectious $A$, symptomatic infectious $I$, recovered $R$ and protected $P$ individuals, with $N=S+A+I+R+P$. Recruitment is $\Lambda$ and natural mortality $\mu$. The transmission rate is $\beta$, reduced by the factor $1-p$ and by the relative infectiousness $\theta$ of asymptomatic cases. Susceptibles move to protection at rate $\phi p$ and protected individuals return at rate $\omega$. Asymptomatic cases become symptomatic at rate $\nu$, and symptomatic cases recover at rate $\delta$:

$$\begin{aligned}
\dot S&=\Lambda-\beta(1-p)\frac{\theta A+I}{N}S-\phi pS+\omega P-\mu S, & \dot A&=\beta(1-p)\frac{\theta A+I}{N}S-(\nu+\mu)A,\\
\dot I&=\nu A-(\delta+\mu)I, & \dot R&=\delta I-\mu R,\qquad \dot P=\phi pS-(\omega+\mu)P .
\end{aligned}$$

**Theorem (constant parameters).**

1. For initial data in the biologically feasible region $\Omega$ there is a unique global nonnegative solution, and $\Omega$ is positively invariant.
2. The disease-free equilibrium is $\Sigma_0=\Big(\frac{\Lambda(\omega+\mu)}{\mu(p\phi+\mu+\omega)},0,0,0,\frac{\phi p\Lambda}{\mu(p\phi+\mu+\omega)}\Big)$, and

$$R_0=\frac{\beta(1-p)\,(\delta\theta+\mu\theta+\nu)\,(\omega+\mu)}{(\delta+\mu)(\nu+\mu)(p\phi+\mu+\omega)} .$$

An endemic equilibrium $\Sigma_+$ exists iff $R_0>1$; its susceptible component is $S_+=S_0/R_0$.
3. If $R_0<1$, $\Sigma_0$ is locally and globally asymptotically stable in $\Omega$.
4. The simplex $\Gamma=\{S+A+I+R+P=\Lambda/\mu\}$ is positively invariant. If $R_0>1$, then $\Sigma_+$ is globally asymptotically stable in $\Gamma\setminus\{A=I=0\}$: it attracts every solution in $\Gamma$ with $A(0)+I(0)>0$. (The source states global stability in all of $\Gamma$, but $\Gamma$ contains $\Sigma_0$, and the face $\{A=I=0\}\cap\Gamma$ is invariant with every solution on it converging to $\Sigma_0$; so the face must be excluded.)

**Theorem (pseudo-periodic solutions).** Let $\alpha_0$ and $\alpha^+$ be parameter sets with $R_0(\alpha_0)<1<R_0(\alpha^+)$, where $\Sigma_0$ has basin $\Omega_0$ under $\alpha_0$ and $\Sigma^+$ has basin $\Omega^+$ under $\alpha^+$. Start at $x_0\in\Omega_0$ and alternate between the systems with parameters $\alpha_0$ and $\alpha^+$ at switching times $T_1<T_2<\dots<T_n$ chosen so that $x(T_i)\in\Omega^+$ for odd $i$ and $x(T_i)\in\Omega_0$ for even $i$, with continuity of $x$ at each $T_i$. Then the solution exists, is unique and stays nonnegative. It exhibits pseudo-oscillations between a neighbourhood of $\Sigma_0$ and a neighbourhood of $\Sigma^+$.

So successive relaxations and tightenings of public-health measures, which push $R_0$ across $1$ in alternation, produce multiple epidemic waves without any intrinsic oscillatory mechanism. The same well-posedness holds for a complex network of non-identical SAIRP nodes coupled by mobility, used to fit regional COVID-19 data.

## Expansion

With infected compartments $(A,I)$, the next-generation matrix has a single nonzero eigenvalue. The product $\frac{\delta\theta+\mu\theta+\nu}{(\delta+\mu)(\nu+\mu)}$ is the expected infectiousness accumulated through the $A$ and $I$ stages, and $\frac{\omega+\mu}{p\phi+\mu+\omega}$ is the unprotected fraction of $S_0$ in $\Lambda/\mu$. Global stability of $\Sigma_0$ uses a Lyapunov function combining Volterra terms $x-x_0-x_0\ln(x/x_0)$ for $S$, $P$ and $N$ with linear terms in the infected compartments. On the invariant simplex $\Gamma$ off the disease-free face $\{A=I=0\}$, global stability of $\Sigma_+$ uses a Volterra-type Lyapunov function $\sum_jc_j\big(x_j-x_j^+-x_j^+\ln(x_j/x_j^+)\big)$. The pseudo-oscillation theorem is a concatenation argument. Under $\alpha_0$ the trajectory enters any neighbourhood of $\Sigma_0$ in finite time. At that moment it lies in $\Omega^+$, so after switching to $\alpha^+$ it reaches any neighbourhood of $\Sigma^+$ in finite time, and the argument repeats.

These are the well-posedness theorem, the equilibrium proposition, the three stability theorems of Section 2, and the pseudo-periodic theorem of Section 4 of the source.

## Proof depends on

- [LaSalle's invariance principle](../../../../Analysis/not-yet-classified/la-salle/lasalle-invariant.md)
- [Threshold theorem, stability half, conditional decay form](../../next-generation-matrix-and-the-basic-reproductio/global-solution-decay-of-r0-lt-one.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)

## Sources

- C. J. Silva, G. Cantin, C. Cruz, R. Fonseca-Pinto et al., "Complex network model for COVID-19: human behavior, pseudo-periodic solutions and multiple epidemic waves", arXiv:2010.02368 (2020). <https://doi.org/10.48550/arXiv.2010.02368>

# Minimum eradication time of an SIR epidemic with time-dependent rates

Fix continuous rates $\beta:[0,\infty)\to[\underline\beta,\overline\beta]$ and $\gamma:[0,\infty)\to[\underline\gamma,\overline\gamma]$ with $0<\underline\beta\le\overline\beta$, $0<\underline\gamma\le\overline\gamma$, and vaccination controls $\alpha\in\mathcal{A}=\{\alpha\in L^\infty([0,\infty)):0\le\alpha\le1\}$. For a starting time $t\ge0$ and initial state $(x,y)$, let $(S,I)$ solve the controlled SIR system

$$\dot S = -\beta(s+t)\,S I - \alpha(s+t)\,S, \qquad \dot I = \beta(s+t)\,S I - \gamma(s+t)\,I, \qquad S(0)=x,\ I(0)=y.$$

Because the rates vary in time, $I$ may oscillate, so for a threshold $\mu>0$ there are two natural eradication times:

$$\overline u^{\alpha}(x,y,t) = \sup\{s\ge0: I(s)\ge\mu\}, \qquad \underline u^{\alpha}(x,y,t) = \inf\{s\ge0: I(s+a)\le\mu\ \ \forall a\ge0\},$$

with value functions $\overline u = \inf_{\alpha}\overline u^{\alpha}$ and $\underline u = \inf_{\alpha}\underline u^{\alpha}$ on $[0,\infty)\times[\mu,\infty)\times[0,\infty)$.

**Theorem.**

1. $\overline u$ is upper semicontinuous and a viscosity subsolution, and $\underline u$ is lower semicontinuous and a viscosity supersolution, of the time-dependent Hamilton-Jacobi equation

$$-\partial_t u + \beta(t)\,x y\,\partial_x u + x\,(\partial_x u)_+ + \bigl(\gamma(t)-\beta(t)x\bigr)\,y\,\partial_y u = 1$$

in $(0,\infty)\times(\mu,\infty)\times(0,\infty)$.

2. (Choice of threshold.) For every $\mu_0>0$ there is $\mu_1\in(0,\mu_0]$, depending only on $\mu_0$ and the rate bounds, such that for every threshold $\mu\in(0,\mu_1]$ the two eradication times agree, $u:=\overline u=\underline u$ on $[0,\infty)\times[\mu_0,\infty)\times[0,\infty)$; $u$ is then a viscosity solution of the equation above in $(0,\infty)\times(\mu_0,\infty)\times(0,\infty)$, and it is the unique nonnegative viscosity solution with its boundary values on $\{y=\mu_0\}$, $\{x=0\}$ and $\{t=0\}$.

3. If moreover the rates are constant, $\beta\equiv\beta_0$ and $\gamma\equiv\gamma_0$, after time $\frac{1}{2\overline\gamma}\log(\mu_0/\mu)$, then $u$ is locally semiconcave.

The key fact behind item 2 is that, starting from $I(0)\ge\mu_0$, every local extremum of $I$ along every controlled trajectory stays above $\mu_1$, so once $I$ drops below a threshold $\mu\le\mu_1$ it can never return above it.

## Expansion

1. Continuity of the flow in the data (with the weak-$*$ topology on controls) and existence of optimal controls give the semicontinuity and the dynamic programming principle.
2. The dynamic programming principle yields the sub- and supersolution properties in the usual way; the Hamiltonian is convex in $\partial_x u$ through the term $x(\partial_x u)_+$, which encodes the optimal bang-bang vaccination choice.
3. A compactness argument over all rate functions and controls bounds the critical values of $I$ from below by some $\mu_1>0$, ruling out oscillations across small thresholds; uniqueness follows from a comparison principle with the given boundary data.

## Sources

- J. Jang, Y. Kim, *On a minimum eradication time for the SIR model with time-dependent coefficients*, arXiv:2311.14657 (Theorems 1, 2 and 3; Section 3). <https://doi.org/10.48550/arXiv.2311.14657> Published version: Proceedings of the American Mathematical Society 153 (2025) 2965–2980, <https://doi.org/10.1090/proc/17156>.

# Global threshold dynamics of the SIRI model with distributed delay and relapse

**Setting.** Susceptibles $s$, infectives $i$ and recovered $r$ satisfy

$$\frac{ds}{dt} = \Lambda - \mu s - \beta\int_0^h g(\tau)\,f\big(s(t), i(t-\tau)\big)\,d\tau, \qquad \frac{di}{dt} = \beta\int_0^h g(\tau)\,f\big(s(t), i(t-\tau)\big)\,d\tau - (\mu + c + \gamma)\,i + \delta r,$$

$$\frac{dr}{dt} = \gamma i - (\mu + \delta)\,r,$$

with recruitment $\Lambda$, natural death $\mu$, disease death $c$, recovery $\gamma$, relapse rate $\delta$ (recovered individuals return to the infective class), transmission coefficient $\beta$, and a nonnegative delay kernel $g$ on $[0,h]$ normalised to $\int_0^h g = 1$. The incidence $f$ is $C^1$ with $f(0,i) = f(s,0) = 0$ and satisfies
- (H1) $f$ is strictly increasing in $s$ and increasing in $i$;
- (H2) $f(s,i)/i$ is bounded and decreasing in $i > 0$.

**Theorem.**
1. Solutions with positive initial data stay positive, and $\Omega = \{s,i,r > 0,\ s + i + r \le \Lambda/\mu\}$ is positively invariant.
2. With disease-free equilibrium $E_0 = (\Lambda/\mu, 0, 0)$, the basic reproduction number is

$$R_0 = \frac{\beta\,(\mu + \delta)\,\partial_i f(E_0)}{(\mu+\delta)(\mu + c + \gamma) - \delta\gamma}.$$

3. Under (H1)–(H2), $E_0$ is globally asymptotically stable if and only if $R_0 \le 1$.
4. If $R_0 > 1$ there is a unique endemic equilibrium $E^\ast$, and under (H1)–(H2) it is globally asymptotically stable.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

The denominator of $R_0$ is the effective removal rate from the infective class once relapse is accounted for: an infective leaves at rate $\mu + c + \gamma$, but a fraction $\gamma\cdot\delta/(\mu+\delta)$ of that outflow returns, so the mean infectious period is $(\mu+\delta)/\big((\mu+\delta)(\mu+c+\gamma) - \delta\gamma\big)$; multiplying by the linearised force of infection $\beta\,\partial_i f(E_0)$ gives $R_0$. The distributed delay does not change $R_0$ because the kernel integrates to one. Global stability is proved with Volterra-type Lyapunov functionals of the form $\sum (x - x^\ast - x^\ast\ln(x/x^\ast))$ plus an integral term over the delay window, $\int_0^h g(\tau)\int_{t-\tau}^t \Phi(i(\theta))\,d\theta\,d\tau$, which absorbs the history; (H2) makes the incidence concave enough in $i$ for the functional to decrease, and LaSalle's invariance principle concludes. The result covers bilinear, saturated and Beddington–DeAngelis-type incidences simultaneously.

## Sources

- Abdelhai Elazzouzi, Abdesslem Lamrani Alaoui, Mouhcine Tilioua, Delfim F. M. Torres, "Analysis of a SIRI Epidemic Model with Distributed Delay and Relapse", Statistics, Optimization & Information Computing 7 (2019), <https://doi.org/10.19139/soic-2310-5070-831>. Published version of arXiv:1812.09626, cited next; locators there refer to the arXiv version.
- Abdelhai Elazzouzi, Abdesslem Lamrani Alaoui, Mouhcine Tilioua, Delfim F. M. Torres, "Analysis of a SIRI epidemic model with distributed delay and relapse", arXiv:1812.09626 (2018), Section 2 (model), Section 3 (hypotheses (H1)–(H3), Theorems 1 and 2), Section 4 (Lemma 1, Theorems 3 and 4), <https://doi.org/10.48550/arXiv.1812.09626>.

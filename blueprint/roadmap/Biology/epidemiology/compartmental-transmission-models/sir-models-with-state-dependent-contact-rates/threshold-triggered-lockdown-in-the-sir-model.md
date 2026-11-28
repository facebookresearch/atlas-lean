# Threshold-triggered lockdown in the SIR model and its sliding plateau

In the [SIR model with state-dependent contact rate](single-peak-dynamics-of-sir-with-state-dependent-contact-rate.md) take the discontinuous lockdown policy

$$f(y) = \begin{cases} \beta, & y < k, \\ \bar\beta, & y \ge k, \end{cases} \qquad 0 < \bar\beta < \beta,$$

which reduces contacts once the infected fraction reaches the threshold $k$. Write $\rho = \gamma/\beta$, $\bar\rho = \gamma/\bar\beta$, and interpret solutions in the sense of Filippov. The segment $\{(x,k) : \rho \le x \le \min\{\bar\rho,1\}\}$ is a sliding manifold. Start from $(x,y,z)(0) = (1-\epsilon,\epsilon,0)$ with $(1-\epsilon)/\rho > 1$, let $M(\epsilon,\rho) = 1 - \rho + \rho\ln\rho - \rho\ln(1-\epsilon)$ be the uncontrolled peak, and

$$m(\epsilon,\rho,\bar\rho) = \begin{cases} 1 - \bar\rho + \rho\ln\dfrac{\bar\rho}{1-\epsilon}, & \rho < \bar\rho < 1-\epsilon, \\ \epsilon, & 1 - \epsilon < \bar\rho. \end{cases}$$

**Theorem.**

1. If $M(\epsilon,\rho) < k$, the threshold is never reached, the solution is that of the uncontrolled $\beta$-SIR model, and $y^{\max} = M(\epsilon,\rho)$.
2. If $m(\epsilon,\rho,\bar\rho) < k < M(\epsilon,\rho)$, there are times $0 < t^* < t^{**}$ with $y(t) = k$ on $[t^*,t^{**}]$ (a plateau sliding along the threshold), $y$ increasing on $[0,t^*]$ and decreasing to $0$ on $[t^{**},\infty)$; the peak is exactly $k$.
3. If $\rho < \bar\rho < 1-\epsilon$ and $\epsilon \le k \le m(\epsilon,\rho,\bar\rho)$, the infection curve has a single peak at some $t^*$, followed by monotone decay to $0$, with

$$y^{\max} = M(\epsilon,\bar\rho) + (\bar\rho - \rho)\ln\frac{1-\epsilon}{x(k)},$$

where $x(k)$, the susceptible fraction at which the orbit first crosses $y = k$, is the root in $(\rho, 1-\epsilon)$ of $x(k) - \rho\ln x(k) + \rho\ln(1-\epsilon) + k - 1 = 0$, obtained from the first integral $x + y - \rho\ln x$ of the uncontrolled orbit. (The source\'s equation (10) has the signs of the two logarithmic terms reversed.)
4. If $\bar\rho > 1-\epsilon$ and $k = m(\epsilon,\rho,\bar\rho) = \epsilon$, the initial point lies on the sliding segment: the solution slides along $y = \epsilon$ from $t = 0$ until $x$ reaches $\rho$, then decreases to $0$, and $y^{\max} = \epsilon$ (a plateau, not a single peak). The source's Theorem 2(c) applies the formula of item 3 to this case too, which would give $M(\epsilon,\bar\rho) > \epsilon$.

So a threshold policy can cap the epidemic peak at exactly $k$ only in the intermediate regime; for low thresholds the lockdown is triggered while $x > \bar\rho$ and the reduced epidemic still grows past $k$.

## Depends on

- [Single-peak dynamics of SIR epidemics with state-dependent contact rates](single-peak-dynamics-of-sir-with-state-dependent-contact-rate.md)

## Expansion

In each region the planar $(x,y)$ system is a classical SIR system with first integral $x + y - \rho\ln x$ (respectively with $\bar\rho$). On $y = k$ the vector field above points down when $\bar\beta x < \gamma$ and the field below points up when $\beta x > \gamma$, so for $\rho < x < \bar\rho$ the Filippov convex combination slides along $y = k$ with $\dot x = -\gamma k$, until $x$ reaches $\rho$ and the orbit leaves into the region below. Matching the uncontrolled orbit to the first crossing gives $x(k)$; if the orbit crosses with $x(k) > \bar\rho$, it follows the $\bar\beta$-orbit through $(x(k),k)$, whose maximum is computed from the $\bar\rho$ first integral, yielding the stated $y^{\max}$. The boundary $k = m(\epsilon,\rho,\bar\rho)$ is the threshold at which the uncontrolled orbit crosses $y = k$ exactly at $x = \bar\rho$.

## Sources

- Martina Alutto, Giacomo Como, Fabio Fagnani, "On SIR epidemic models with feedback-controlled interactions and network effects", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 5562–5567, <https://doi.org/10.1109/cdc45484.2021.9683007>. Published version of arXiv:2105.01538, cited next; locators there refer to the arXiv version.
- Martina Alutto, Giacomo Como, Fabio Fagnani, "On SIR epidemic models with feedback-controlled interactions and network effects", arXiv (2021). Section 3, Theorem 2. <https://doi.org/10.48550/arXiv.2105.01538>

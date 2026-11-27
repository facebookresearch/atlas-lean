# Ergodicity and extinction thresholds of the stochastic SIQS model with Lévy jumps

**Model.** Susceptible $S$, infected $I$ and quarantined $Q$ individuals, with recruitment $A$, death rates $\mu_1,\mu_2,\mu_3$, transmission $\beta$, recovery $\gamma$, quarantine rate $\delta$ and release rate $k$, under white noise and Lévy jumps:

$$\begin{aligned}
dS &= \big(A - \mu_1S - \beta SI + \gamma I + kQ\big)dt + \sigma_1S\,dW_1 + \int_Z\eta_1(u)S(t^-)\widetilde{N}(dt,du) - \sigma_\beta SI\,dW_\beta,\\
dI &= \big(\beta SI - (\mu_2 + \delta + \gamma)I\big)dt + \sigma_2I\,dW_2 + \int_Z\eta_2(u)I(t^-)\widetilde{N}(dt,du) + \sigma_\beta SI\,dW_\beta,\\
dQ &= \big(\delta I - (\mu_3 + k)Q\big)dt + \sigma_3Q\,dW_3 + \int_Z\eta_3(u)Q(t^-)\widetilde{N}(dt,du).
\end{aligned}$$

The noise $\sigma_\beta\,dW_\beta$ perturbs the transmission rate; $\widetilde{N}$ is a compensated Poisson random measure with Lévy measure $\nu$ on $Z\subseteq(0,\infty)$, $\nu(Z)<\infty$, and the $\eta_i$ are bounded. Write $\bar\sigma=\max_i\sigma_i^2$, $\bar\eta=\max_i\eta_i$, $\underline\eta=\min_i\eta_i$, $\hat\rho_{n,p}(u)=(1+\bar\eta(u))^{np}-1-np\,\bar\eta(u)$, $\check\rho_{n,p}(u)=(1+\underline\eta(u))^{np}-1-np\,\underline\eta(u)$ and $\ell_{n,p}=\int_Z\hat\rho_{n,p}\vee\check\rho_{n,p}\,d\nu$. The source assumes throughout:
- (A1) $\int_Z\eta_i^2\,d\nu<\infty$ for $i=1,2,3$;
- (A2) $1+\eta_i(u)>0$ for all $u\in Z$, and $\int_Z\big(\eta_i-\ln(1+\eta_i)\big)\,d\nu<\infty$;
- (A3) $\int_Z\big(\ln(1+\eta_i)\big)^2\,d\nu<\infty$;
- (A4) $\int_Z\big((1+\bar\eta)^2-1\big)^2\,d\nu<\infty$;
- (A5) for each positive integer $n$ there is $p>1$ with $\Gamma_{n,p}=\mu_1-\frac{np-1}{2}\bar\sigma-\frac{\ell_{n,p}}{np}>0$.

Let $\chi = 2\mu_1 - \bar\sigma - \int_Z[\bar\eta^2\vee\underline\eta^2]\,d\nu > 0$ and put $\Lambda_2 = \int_Z\big(\eta_2(u) - \ln(1+\eta_2(u))\big)\nu(du)$ and $c_I = \mu_2 + \delta + \gamma + \sigma_2^2/2$. Define

$$\mathcal{R}^s_0 = \frac{1}{c_I}\Big(\frac{\beta A}{\mu_1} - \frac{A^2\sigma_\beta^2}{\mu_1\chi} - \Lambda_2\Big), \qquad \widehat{\mathcal{R}}^s_0 = \frac{1}{c_I}\Big(\frac{\beta A}{\mu_1} - \frac{\sigma_\beta^2A^2}{2\mu_1^2} - \Lambda_2\Big).$$

**Theorem.** For any initial value in $\mathbb{R}^3_+$:

*(1)* (Ergodicity) If $\mathcal{R}^s_0 > 1$, the system has a unique stationary distribution and is ergodic.

*(2)* (Persistence in the mean) If $\mathcal{R}^s_0 > 1$, then $\liminf_{t\to\infty}\frac1t\int_0^tI(s)\,ds > 0$ almost surely, with an explicit lower bound proportional to $\mathcal{R}^s_0 - 1$.

*(3)* (Extinction) If either $\widehat{\mathcal{R}}^s_0 < 1$ and $\sigma_\beta^2 \le \mu_1\beta/A$, or

$$\frac{\beta^2}{2\sigma_\beta^2} - c_I - \Lambda_2 < 0,$$

then $\limsup_{t\to\infty}\frac{\ln I(t)}{t} < 0$ almost surely; in the first case the exponent is at most $c_I(\widehat{\mathcal{R}}^s_0 - 1)$.

## Expansion

Without noise the threshold would be $\beta A/(\mu_1(\mu_2+\delta+\gamma))$, with $A/\mu_1$ the disease-free susceptible level. Applying Itô's formula with jumps to $\ln I$ gives growth rate $\beta S - c_I - \frac12\sigma_\beta^2S^2 - \Lambda_2$ plus martingale terms; white noise on $I$ adds $\sigma_2^2/2$ to the effective removal rate, jumps subtract the nonnegative $\Lambda_2$ from the transmission gain, and transmission noise costs a term quadratic in $S$. Bounding the time averages of $S$ and $S^2$ by the total-population process (whose second moment is controlled through $\chi$) gives $\mathcal{R}^s_0$ for persistence; a Lyapunov function and Khasminskii-type criteria give a stationary distribution. Maximizing the quadratic in $S$ gives the second extinction condition $\beta^2/(2\sigma_\beta^2) < c_I + \Lambda_2$: strong transmission noise alone can eradicate the disease.

## Sources

- Driss Kiouach, Yassine Sabbar and Salim El Azami El-idrissi, "New results on the asymptotic behavior of an SIS epidemiological model with quarantine strategy, stochastic transmission, and Lévy disturbance", arXiv:2012.00875 (2020), Section 2 and Section 3, Theorems 3.1-3.3, <https://doi.org/10.48550/arXiv.2012.00875>.

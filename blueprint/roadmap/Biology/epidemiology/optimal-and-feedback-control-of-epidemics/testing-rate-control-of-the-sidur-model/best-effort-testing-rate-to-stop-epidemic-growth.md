# Best-effort testing rate to stop epidemic growth

**Model (SIDUR).** A closed population of size $N$ is split into susceptible $x_S$, undetected infected $x_I$, detected (isolated) infected $x_D$, unidentified recovered $x_U$ and identified removed $x_R$. Only undetected infected individuals transmit, and $u(t)\ge 0$ tests per day are spread over the *testable population*

$$
x_T(t) = x_I(t) + (1-\theta)\bigl(x_S(t) + x_U(t)\bigr),
$$

where $\theta\in[0,1]$ is the testing specificity parameter (each test detects an infected person with probability $x_I/x_T$). The dynamics are

$$
\begin{aligned}
\dot x_S &= -\beta x_S \frac{x_I}{N}, &
\dot x_I &= \beta x_S \frac{x_I}{N} - u\frac{x_I}{x_T} - \gamma x_I, &
\dot x_D &= u\frac{x_I}{x_T} - \rho x_D, \\
\dot x_U &= \gamma x_I, &
\dot x_R &= \rho x_D, & &
\end{aligned}
$$

with infection rate $\beta(t)\ge 0$, recovery rate $\gamma>0$ and removal rate $\rho>0$. The effective reproduction number is $R(t) = \dfrac{\beta(t)}{u(t)/x_T(t) + \gamma}\dfrac{x_S(t)}{N}$, and $\dot x_I = \bigl(\beta x_S/N - u/x_T - \gamma\bigr)x_I$.

**Proposition (BEST policy).** Let

$$
c^*(t) = x_T(t)\left[\frac{\beta(t)}{N}x_S(t) - \gamma\right]_+ ,
$$

where $[z]_+ = \max\{z,0\}$. Suppose that on an interval $[t^*,t_1)$ the infection rate $\beta$ is non-increasing and the testing specificity $\theta$ is non-decreasing. Then the constant testing rate $u(t) = c^*(t^*)$ for $t\in[t^*,t_1)$ is the smallest testing rate that switches the epidemic from spreading to non-spreading at $t^*$. Any $u\ge c^*(t^*)$ on $[t^*,t_1)$ makes $x_I$ non-increasing there (decreasing if the inequality is strict), while a rate below $c^*(t^*)$ lets the epidemic keep spreading.

## Expansion

If $u(t)>c^*(t)$, the per-capita growth rate of $x_I$ is negative, so $x_I$ decreases. To get the same conclusion from the *constant* rate $c^*(t^*)$, note that while $x_I$ decreases and $\theta$ does not decrease, $x_T$ decreases. Since $x_S$ always decreases and $\beta$ does not increase, $c^*(t)$ decreases too. Hence $c^*(t^*)>c^*(t)$ persists on a maximal interval, and a continuation argument extends it to all of $[t^*,t_1)$. Because $c^*$ scales with $x_T$ and with the excess growth rate, the required testing rate rises steeply when testing starts late. The monotonicity hypotheses are essential: an increase in $\beta$ (for example, lifting a lockdown) or a fall in $\theta$ (less targeted testing) can make the frozen rate insufficient.

## Sources

- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, Liudmila Tumash, Pierre-Alexandre Bliman, "Effective Testing Policies for Controlling an Epidemic Outbreak", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 2806–2811, <https://doi.org/10.1109/cdc45484.2021.9683300>. Published version of arXiv:2109.12553, cited next; locators there refer to the arXiv version.
- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, Liudmila Tumash, Pierre-Alexandre Bliman, "Effective Testing Policies for Controlling an Epidemic Outbreak", arXiv 2021: Section 2 (SIDUR model, Assumption 1), Section 3, Proposition 3. <https://doi.org/10.48550/arXiv.2109.12553>
- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, Liudmila Tumash, Pierre-Alexandre Bliman, "Modeling and control of epidemics through testing policies", Annual Reviews in Control 52 (2021), 554–572, <https://doi.org/10.1016/j.arcontrol.2021.09.004>. Published version of arXiv:2010.15438, cited next; locators there refer to the arXiv version.
- Muhammad Umar B. Niazi, Alain Kibangou, Carlos Canudas-de-Wit, Denis Nikitin, "Modeling and Control of Epidemics through Testing Policies", arXiv:2010.15438 (2020), Section 2 (SIDUR model, testable population, reproduction numbers), Proposition 1, Lemma 6. <https://doi.org/10.48550/arXiv.2010.15438>

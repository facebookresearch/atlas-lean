# Hinge model of log viral load and the test-detectable window

In the hinge model, the log viral load $v(t) = \log_{10} V(t)$ (copies/ml) of an infected person, $t$ in days since exposure, is the continuous piecewise-linear function through the control points

$$(t_0, 3), \qquad (t_p, v_p), \qquad (t_f, 6), \qquad t_0 < t_p < t_f,\ v_p > 6,$$

rising linearly from $t_0$ to the peak $t_p$ and decaying linearly afterwards (continuing below 6 until recovery at $v = 3$). For SARS-CoV-2 the control points were drawn as $t_0 \sim U[2.5, 3.5]$, $v_p \sim U[7, 11]$, $t_p - t_0 \sim 0.5 + \mathrm{Gamma}(1.5)$ capped at 3; for asymptomatic infections $t_f - t_p \sim U[4, 9]$, and for symptomatic ones symptom onset $t_s - t_p \sim U[0, 3]$ and $t_f - t_s \sim U[4, 9]$. A person is infectious while $v(t) > 6$, with log-proportional infectiousness $F(t) \propto (v(t) - 6)_+$.

For a test with limit of detection $10^{\ell}$, $3 \le \ell < v_p$, the following hold.

1. The detectable window $\{t \ge t_0 : v(t) \ge \ell\}$ is the interval $[a_\ell, b_\ell]$ with

$$a_\ell = t_0 + \frac{(\ell - 3)(t_p - t_0)}{v_p - 3}, \qquad b_\ell = t_p + \frac{(v_p - \ell)(t_f - t_p)}{v_p - 6}.$$

2. The infectious window is $(a_6, t_f)$, and it is contained in $[a_\ell, b_\ell]$ if and only if $\ell \le 6$. Every test with limit of detection at most $10^6$ can therefore detect the infection on every infectious day, and becomes positive $(6 - \ell)(t_p - t_0)/(v_p - 3)$ days before infectiousness begins.
3. The total log-proportional infectiousness is the area of a triangle:

$$\int (v(t) - 6)_+\, dt = \frac{v_p - 6}{2} \Big(\frac{(v_p - 6)(t_p - t_0)}{v_p - 3} + (t_f - t_p)\Big).$$

Alternative infectiousness functions, proportional to $V(t) \cdot 10^{-6}$ above the threshold or constant above it, were used as sensitivity analyses.

## Remarks

On the rising segment $v(t) = 3 + (v_p - 3)(t - t_0)/(t_p - t_0)$ and on the falling segment $v(t) = v_p - (v_p - 6)(t - t_p)/(t_f - t_p)$; solving $v = \ell$ on each gives $a_\ell$ and $b_\ell$, and $b_\ell \ge t_f = b_6$ exactly when $\ell \le 6$. The function $(v - 6)_+$ is a tent of height $v_p - 6$ over the infectious window, whose length is $(t_p - a_6) + (t_f - t_p)$. With limits of detection $10^3$ (PCR) and $10^5$ (rapid antigen tests), both sit below the culture threshold $10^6$, so a test that is taken during the infectious window detects the infection; the gap between the two classes of test is only the short pre-infectious lead $(\ell - 3)(t_p - t_0)/(v_p - 3)$, between about 0.1 and 1.5 days for the sampled control points.

## Sources

- D. B. Larremore et al., "Test sensitivity is secondary to frequency and turnaround time for COVID-19 screening", Science Advances 7 (2021), eabd5393, Materials and Methods (sections "Viral loads" and "Infectiousness") and Fig. 7, <https://doi.org/10.1126/sciadv.abd5393>, PMCID: PMC7775777.

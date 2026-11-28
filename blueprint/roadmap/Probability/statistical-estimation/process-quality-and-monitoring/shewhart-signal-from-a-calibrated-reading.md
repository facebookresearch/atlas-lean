# Shewhart signal from a calibrated reading

Let $\mu_0$ be a centre line, $\sigma_0 > 0$ and $h > 0$, and call a value $x$ a signal when $\lvert x - \mu_0\rvert > h\sigma_0$, that
is, when it lies outside the control limits $\mu_0 \pm h\sigma_0$. Let $\hat x$ be a calibrated reading with
$\lvert \hat x - x\rvert \le \varepsilon$, $\varepsilon \ge 0$. If $\lvert \hat x - \mu_0\rvert > h\sigma_0 + \varepsilon$, then $x$ is a
signal; if $\lvert \hat x - \mu_0\rvert \le h\sigma_0 - \varepsilon$, then $x$ is not. Otherwise the reading does not decide, and an
undecided reading is not evidence that there is no signal. The calibration bound is an assumption about the instrument on the
population where it was validated.

## Sources

- NIST/SEMATECH *e-Handbook of Statistical Methods*, Section 6.3.2, Shewhart control limits $\mu_w \pm k\sigma_w$ and the average run length, <https://www.itl.nist.gov/div898/handbook/pmc/section3/pmc32.htm>.

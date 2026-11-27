# Infectiousness removed by periodic screening with a turnaround delay

Fix one infected person with nonnegative daily infectiousness $F(t)$, $t \in \mathbb{Z}$, not identically zero, and daily viral loads $V(t)$. A screening programme tests the person every $D \ge 1$ days on the days $t \equiv \varphi \pmod D$, with phase $\varphi$ uniform on $\{0, \dots, D - 1\}$ and independent of the infection. A test on day $t$ is positive if and only if $V(t) > L$, the limit of detection, and a positive test on day $t$ leads to isolation on day $t + T$, where $T \ge 0$ is the sample-to-answer turnaround time. A symptomatic person also self-isolates on day $t_s$ (set $t_s = +\infty$ otherwise). Let

$$\Delta_L = \{t : V(t) > L\}, \qquad \tau_\varphi = \min\{t \in \Delta_L : t \equiv \varphi \pmod D\}, \qquad t_{\mathrm{iso}} = \min(\tau_\varphi + T,\ t_s),$$

with $\min \emptyset = +\infty$, and define the fraction of infectiousness removed

$$r(\varphi; D, L, T) = \frac{\sum_{t \ge t_{\mathrm{iso}}} F(t)}{\sum_t F(t)}.$$

Then:

1. $r$ is nonincreasing in the turnaround time $T$.
2. $r$ is nonincreasing in the limit of detection $L$: a less sensitive test can never remove more infectiousness for the same testing days.
3. If $\Delta_L$ contains $D$ consecutive days starting at $t_d = \min \Delta_L$, then every phase detects and $\tau_\varphi \le t_d + D - 1$; with daily testing, $\tau_\varphi = t_d$.
4. In a population of independent infected individuals whose expected number of secondary infections is proportional to the infectiousness emitted before isolation, the reproduction number under screening is

$$R = R_{\mathrm{sym}} \cdot \frac{\mathbb{E}\big[\sum_{t < t_{\mathrm{iso}}} F(t)\big]}{\mathbb{E}\big[\sum_{t < t_s} F(t)\big]},$$

where $R_{\mathrm{sym}}$ is the reproduction number with symptom-driven self-isolation only and expectations are over individuals and phases; it is a ratio of expectations, not the mean of individual ratios.

In simulations with a hinge viral load model, 35% of infected people isolating within 3 days of peak viral load, and limits of detection $10^3$ and $10^5$, weekly screening removed 62–66% of individuals' total infectiousness and testing every two weeks removed 45–47%, with little difference between the two tests; in population models, faster turnaround and more frequent testing reduced $R$ and outbreak size far more than higher analytical sensitivity.

## Depends on

- [Hinge model of log viral load and the test-detectable window](hinge-model-of-log-viral-load-and-the-test-detectable-window.md)

## Proof sketch

Increasing $T$ moves $t_{\mathrm{iso}}$ later, and $F \ge 0$, so the removed tail shrinks. Increasing $L$ shrinks $\Delta_L$, so the minimum $\tau_\varphi$ over a smaller set of testing days can only increase. Any $D$ consecutive integers contain exactly one day in each residue class modulo $D$, which gives the detection-delay bound. For item 4, summing expected offspring over the infectiousness actually emitted and normalizing by the same quantity without screening gives the ratio. With a hinge trajectory, a test whose limit of detection is below the infectiousness threshold detects throughout the infectious window, so frequency and turnaround control when the window is cut, while sensitivity only shifts the first detectable day by a fraction of the rising phase.

## Sources

- D. B. Larremore et al., "Test sensitivity is secondary to frequency and turnaround time for COVID-19 screening", Science Advances 7 (2021), eabd5393, Results ("Impact of repeated population screening on individuals", Fig. 1) and Materials and Methods ("Testing, isolation, and sample-to-answer turnaround times", "Calibration to achieve targeted R0 and estimation of R"), <https://doi.org/10.1126/sciadv.abd5393>, PMCID: PMC7775777.

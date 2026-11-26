# Censored and truncated likelihood for epidemiological delays

Let a delay (onset to death, or the serial interval between infector and infectee onsets) have density $f(\cdot \mid \theta)$ and distribution function $F(\cdot \mid \theta)$ on $[0, \infty)$, and let the observations be independent. Each observation contributes one factor according to what is known about its delay $V$:

| observation | known information | likelihood factor |
|---|---|---|
| exact | $V = v$ | $f(v \mid \theta)$ |
| right-censored | $V > v^{L}$ | $1 - F(v^{L} \mid \theta)$ |
| interval-censored | $v^{L} < V \le v^{U}$ | $F(v^{U} \mid \theta) - F(v^{L} \mid \theta)$ |
| left-truncated at $v^{*}$ | the pair is observed only because $V > v^{*}$ | divide the factor above by $1 - F(v^{*} \mid \theta)$ |

For onset-to-death delays where the onset date is known for the cases in a set $A$ and only the admission-to-death time $v_j^{L}$ (a lower bound) for the cases in $B$,
$$L_{\mathrm{od}}(\theta) = \prod_{j \in A} f(v_j \mid \theta) \prod_{j \in B} \bigl(1 - F(v_j^{L} \mid \theta)\bigr).$$
For serial intervals with exact values $s_j$ ($j \in A$), ranges $(s_j^{L}, s_j^{U}]$ ($j \in B$) and truncation bounds $s_j^{*}$ imposed by the infector's travel history,
$$L_{\mathrm{SI}}(\theta) = \prod_{j \in A} \frac{f(s_j \mid \theta)}{1 - F(s_j^{*} \mid \theta)} \prod_{j \in B} \frac{F(s_j^{U} \mid \theta) - F(s_j^{L} \mid \theta)}{1 - F(s_j^{*} \mid \theta)},$$
with $s_j^{*} = 0$ (so the denominator is $1$) when no bound applies.

Each factor is the probability (or density) of the observed event conditional on the selection event, so the product is the exact likelihood under independence, and maximizing or sampling from it yields consistent estimates of $\theta$ under the parametric model, whereas treating lower bounds as exact delays biases the delay distribution towards shorter values.

## Expansion

For a right-censored case the only information is that the true delay exceeds the observed lower bound, whose probability is the survival function; for a range the probability is the increment of $F$; and a truncation bound conditions on $V > v^*$, dividing by $\Pr(V > v^*)$. In the Wuhan severity analysis both delays are gamma with unknown mean and standard deviation, these two factors enter the joint likelihood alongside Poisson, binomial and multinomial factors for case, prevalence, death and age-distribution data, and the joint posterior is sampled by Markov chain Monte Carlo; the estimated mean serial interval was about $7.0$ days.

## Sources

- J. T. Wu, K. Leung, M. Bushman, et al., "Estimating clinical severity of COVID-19 from the transmission dynamics in Wuhan, China", Nature Medicine 26 (2020) 506–510, Methods, likelihood components for onset-to-death delays and serial intervals, <https://doi.org/10.1038/s41591-020-0822-7> (PMC7094929).

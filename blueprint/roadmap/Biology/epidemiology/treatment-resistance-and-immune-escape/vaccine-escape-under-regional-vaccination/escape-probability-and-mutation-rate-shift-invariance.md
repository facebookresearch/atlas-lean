# Escape probability of a rare resistant mutant and mutation-rate shift invariance

Fix a configuration $c$ (a vaccination regime and all model parameters except the per-infection mutation probability $\mu$) over a campaign $[0, T]$. Let $x(t, c) \ge 0$ be the stream of new infections at time $t$ and $p(t, c) \in [0, 1)$ the probability that a vaccine-resistant mutant arising at time $t$ takes over, assuming no other mutant arises; both are integrable and do not depend on $\mu$. Treating mutant arrivals as independent, the probability that at least one mutant arises and takes over is the product integral

$$P(c, \mu) = 1 - \prod_{t=0}^{T} \big(1 - p(t, c)\big)^{\mu\, x(t, c)\, dt}, \qquad \ln\big(1 - P(c, \mu)\big) = \mu \int_0^T x(t, c) \ln\big(1 - p(t, c)\big)\, dt.$$

Write $A(c) = -\int_0^T x(t, c) \ln(1 - p(t, c))\, dt \ge 0$, so $P(c, \mu) = 1 - e^{-\mu A(c)}$. Then:

1. (shift invariance) if $P(c_1, \mu_1) = P(c_2, \mu_2)$, then $P(c_1, \alpha \mu_1) = P(c_2, \alpha \mu_2)$ for every $\alpha > 0$;
2. if $A(c_1), A(c_2) > 0$, then $P(c_1, \mu) = P\big(c_2, \mu A(c_1)/A(c_2)\big)$ for all $\mu$, so plotted against $\log_{10} \mu$ the escape-probability curves of the two configurations are horizontal translates of each other by $\log_{10}\big(A(c_1)/A(c_2)\big)$.

The single number $\log_{10}(A(c_1)/A(c_2))$, in orders of magnitude of mutation rate, therefore compares the escape risk of two regimes uniformly over all escape probabilities.

## Proof sketch

Taking logarithms turns the product integral into $\mu$ times a $\mu$-free integral. Equal escape probabilities mean $\mu_1 A(c_1) = \mu_2 A(c_2)$, and multiplying both sides by $\alpha$ gives item 1. Item 2 is the same identity with $\mu_2 = \mu A(c_1)/A(c_2)$. A difference or ratio of escape probabilities would instead depend on where on the curve it is taken. In the application, an SIR model of COVID-19-like spread in which adaptive social distancing holds the wild type's effective reproduction number near one, so that infections continue throughout a slow vaccination campaign, a uniform one-year campaign adds about 0.8 orders of magnitude of escape risk over instantaneous vaccination. Sequential regional vaccination with ten regions recovers about 0.42 of those orders: it tolerates a mutation probability about 2.6 times higher for the same escape risk.

## Sources

- X. Zhang, G. Lobinska, M. Feldman, E. Dekel, M. A. Nowak, Y. Pilpel, Y. Pauzner, B. Barzel and A. Pauzner, "A spatial vaccination strategy to reduce the risk of vaccine-resistant variants", PLoS Computational Biology 18 (2022) e1010391, Section 2A ("A measure for differences in escape risk", Claim and proof; "Quantifying the differences in escape risk", Figure 4), <https://doi.org/10.1371/journal.pcbi.1010391>, PMCID: PMC9394842.

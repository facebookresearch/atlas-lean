# IICR of a stationary population with heterogeneous effective size along the genome

Consider a stationary panmictic population in which a fraction $a_i > 0$ of the genome ($\sum_{i=1}^K a_i = 1$) evolves with
constant relative effective size $\lambda_i > 0$, $i = 1, \dots, K$ (for example through linked selection). Writing $\mu_i = 1/\lambda_i$,
the pairwise coalescence time at a random genomic position is a mixture of exponentials:

$$R(t) = \Pr(T_2 \ge t) = \sum_{i=1}^K a_i e^{-\mu_i t}.$$

**Proposition.** The [IICR](iicr-of-a-pairwise-coalescence-time.md) of $T_2$ is

$$\mathrm{IICR}(t) = \frac{\sum_{i=1}^K a_i e^{-\mu_i t}}{\sum_{i=1}^K a_i \mu_i e^{-\mu_i t}},$$

and, whenever at least two distinct $\lambda_i$ have positive weight:
1. $\mathrm{IICR}$ is strictly increasing on $[0, \infty)$ (backward in time);
2. $\mathrm{IICR}(0) = \bigl(\sum_i a_i/\lambda_i\bigr)^{-1}$, the $a$-weighted harmonic mean of the $\lambda_i$;
3. $\lim_{t\to\infty} \mathrm{IICR}(t) = \max_i \lambda_i$, regardless of the weight of the largest class.

Hence a population of constant size with heterogeneous $N_e$ along the genome produces an IICR that, read forward in time, decreases,
mimicking a population decline.

## Depends on

- [Inverse instantaneous coalescence rate of a pairwise coalescence time](iicr-of-a-pairwise-coalescence-time.md)

## Proof depends on

None beyond the definition of the IICR listed above; the proof differentiates the mixture hazard directly, as the Expansion describes.

## Expansion

Write $\mathrm{IICR}(t)^{-1} = \sum_i \mu_i w_i(t)$ with weights $w_i(t) = a_i e^{-\mu_i t}/\sum_k a_k e^{-\mu_k t}$, the posterior
probability of class $i$ given $T_2 \ge t$. Its derivative is $-\operatorname{Var}_{w(t)}(\mu) < 0$ when two classes with distinct
$\mu_i$ have positive weight, so the hazard decreases and the IICR increases. At $t = 0$ the weights are $a_i$, and as $t \to \infty$
they concentrate on the class with the smallest $\mu_i$, i.e. the largest $\lambda_i$. This is the classical fact that a mixture of
exponentials has decreasing failure rate. (Boitard et al. 2022, Equations 1–4; monotonicity proved in their Text S1.)

## Sources

- S. Boitard, A. Arredondo, C. Chikhi, and O. Mazet, "Heterogeneity in effective size across the genome: effects on the inverse instantaneous coalescence rate (IICR) and implications for demographic inference under linked selection", Genetics (2022), <https://doi.org/10.1093/genetics/iyac008> (PMC8893248).

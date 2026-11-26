# Bayes-optimal discrimination of proportional population-size histories

Under the variable-size Kingman coalescent, the coalescence time $X$ of a sample of two genes satisfies $P(X > x) = \exp\bigl(-\int_0^x N(s)^{-1}\,ds\bigr)$ for an effective population-size trajectory $N(s) > 0$. Consider the simple hypotheses

$$H_1: N(s) = N_1(s), \qquad H_2: N(s) = c\,N_1(s), \qquad 0 < c < 1,$$

with equal prior probabilities, and let the classifier choose the hypothesis with the larger posterior. Then:

1. from one pairwise coalescence time, the probability of correct classification is

$$P[\text{correct}] = \frac12\,c^{\frac{c}{1-c}} + \frac12\Bigl(1 - c^{\frac{1}{1-c}}\Bigr);$$

2. from $J$ independent pairwise coalescence times (unlinked loci),

$$P[\text{correct}] = \frac12\Bigl(1 - \frac{\gamma\bigl(J,\ \tfrac{Jc\log(1/c)}{1-c}\bigr)}{\Gamma(J)} + \frac{\gamma\bigl(J,\ \tfrac{J\log(1/c)}{1-c}\bigr)}{\Gamma(J)}\Bigr),$$

where $\gamma(a, x)$ is the lower incomplete gamma function.

Neither probability depends on $N_1$. Even with $J = 100$ loci, a probability $0.95$ of identifying the true history requires roughly $c \le 0.72$ (at $c = 0.75$ the probability is about $0.92$), so modest proportional differences in population size are statistically indistinguishable from pairwise data.

## Depends on

- [Upper incomplete gamma function](../../../../Probability/distributions/continuous/gamma-distribution/incomplete-gamma-tail/upper-incomplete-gamma.md)

## Expansion

Let $\Lambda_1(x) = \int_0^x N_1(s)^{-1}ds$. Under $H_1$, $\Lambda_1(X)$ is a standard exponential; under $H_2$ it is exponential with mean $c$. The likelihood ratio therefore depends on the data only through $W = \sum_j \Lambda_1(X_j)$, which is $\mathrm{Gamma}(J, 1)$ under $H_1$ and $\mathrm{Gamma}(J, c)$ (scale $c$) under $H_2$, and the Bayes rule chooses $H_1$ iff $W > Jc\log(1/c)/(1-c)$. Summing the two conditional probabilities of a correct decision gives both formulas; for $J = 1$ they reduce to the first. The time change removes $N_1$ entirely, which is why the bounds are universal.

## Sources

- J. E. Johndrow and J. A. Palacios, "Exact limits of inference in coalescent models", Theoretical Population Biology (2019), <https://doi.org/10.1016/j.tpb.2018.11.004>, PMCID PMC6541399. Section 6, Theorems 6.1 and 6.2 (Equation 6.2).

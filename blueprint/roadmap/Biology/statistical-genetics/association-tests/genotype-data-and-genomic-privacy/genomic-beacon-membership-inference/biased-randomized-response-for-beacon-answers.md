# Biased randomized response for beacon answers

Let each stored presence bit of a beacon be released through a randomizing device with bias $b \in (0,1)$: with probability $b$ report the true bit; otherwise flip again and report the true bit with probability $b$ and its negation with probability $1-b$. Then

$$\Pr(\text{yes}\mid\text{truth yes}) = b + (1-b)b = 1-(1-b)^2, \qquad \Pr(\text{yes}\mid\text{truth no}) = (1-b)^2,$$

and symmetrically for "no", so each released answer is correct with probability $1-(1-b)^2$. Consequently:

1. The mechanism is $\varepsilon$-differentially private for one bit, with $\varepsilon = \left|\ln\left(\frac{1}{(1-b)^2} - 1\right)\right|$; for $b = \frac12$ this is $\varepsilon = \ln 3$.
2. It has the same output law as the simpler mechanism that reports the true bit with probability $b_1$ and its negation otherwise, when $b_1 = 2b - b^2$.

Applying the device once to the stored data, rather than independently at each query, prevents an adversary from averaging repeated answers to the same query. In the [beacon membership test](beacon-likelihood-ratio-test-reduces-to-counting-yes-answers.md) the perturbation raises the number of queries needed for a given power at the cost of accuracy $1-(1-b)^2$ per answer.

## Depends on

- [Differential privacy](../../../../../ComputerScience/cryptography/differential-privacy/differentially-private.md)
- [Beacon likelihood-ratio test reduces to counting yes answers](beacon-likelihood-ratio-test-reduces-to-counting-yes-answers.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For a "yes" output the likelihood ratio between the two possible true bits is $\bigl(1-(1-b)^2\bigr)/(1-b)^2 = 1/(1-b)^2 - 1$, and for a "no" output it is the same number. Bounding both ratios and their reciprocals by $e^{\varepsilon}$ gives the stated $\varepsilon$, which is the absolute value because the ratio falls below $1$ when $1-(1-b)^2 < (1-b)^2$. Part 2 is the observation that both mechanisms are binary symmetric channels, determined by their probability of a correct answer.

## Sources

- M. M. A. Aziz, R. Ghasemi, M. Waliullah and N. Mohammed, "Aftermath of Bustamante attack on genomic beacon service", BMC Medical Genomics 10 (Suppl. 2) (2017), <https://doi.org/10.1186/s12920-017-0278-x>, PMCID PMC5547468. Algorithms 1 and 2 and Theorem 1.

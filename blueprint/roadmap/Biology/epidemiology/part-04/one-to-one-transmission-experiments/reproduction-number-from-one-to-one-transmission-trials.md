# Reproduction number from one-to-one transmission trials

**Model.** Consider a closed population of $N = 2$ individuals, one infectious and one susceptible, following the Markovian stochastic general (SIR) epidemic with time measured in units of the mean infectious period. The infectious individual recovers at rate $1$ (exponentially distributed infectious period with mean $1$), and while infectious it infects each of the other $N - 1$ individuals at rate $R_0/(N-1)$, so that over its whole infectious period it makes on average $R_0 > 0$ effective contacts; for $N = 2$ the infection rate is $R_0$. (Scaling the mass-action term by $N - 1$ rather than $N$ is what makes $R_0$ the expected number of infectious contacts when $N$ is small.)

**Proposition (transmission probability).** The probability $q$ that the susceptible individual is eventually infected is

$$q = \frac{R_0}{R_0 + 1}, \qquad R_0 = \frac{q}{1 - q}.$$

**Binomial likelihood and estimator.** If $n$ pairs are run independently (no air exchange between pairs) with the same $R_0$, the number $K$ of pairs with successful transmission is $\mathrm{Binomial}(n, q)$:

$$\Pr(K = k) = \binom{n}{k} \left(\frac{R_0}{R_0 + 1}\right)^{k} \left(\frac{1}{R_0 + 1}\right)^{n-k}, \qquad k = 0, \dots, n .$$

Since $q \mapsto q/(1-q)$ is a bijection $[0,1) \to [0, \infty)$, the maximum likelihood estimator of $R_0$ is obtained by equating $q$ with the observed proportion $k/n$:

$$\widehat{R}_0 = \frac{k}{n - k}, \qquad 0 \le k < n,$$

with $\widehat{R}_0 = \infty$ when every pair transmits ($k = n$). Confidence limits for $R_0$ are the images under $q \mapsto q/(1-q)$ of exact binomial confidence limits for $q$; in particular, when $k = n$ only a finite lower limit exists, and when $k = 0$ the lower limit is $0$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

With one infective and one susceptible, the only events are infection of the susceptible (rate $R_0$) and recovery of the infective (rate $1$). The two competing exponential clocks give infection first with probability $R_0/(R_0 + 1)$; once the infective has recovered nothing further can happen, so this is the final-state probability $p_{0,0}(\infty)$ of the differential-difference (Kolmogorov) equations of the stochastic general epidemic started from one susceptible and one infective. The binomial model follows from independence of the pairs, and invariance of maximum likelihood under the reparametrization $R_0 = q/(1-q)$ gives $\widehat{R}_0$. The relation depends on the experimental design (air flow, exchange rate, inoculation dose), so values of $R_0$ are comparable only within a design.

## Sources

- H. Nishiura, H.-L. Yen and B. J. Cowling, "Sample size considerations for one-to-one animal transmission studies of the influenza A viruses", PLoS ONE 8 (2013), e55358, Materials and Methods, Eqs. (1)–(5), <https://doi.org/10.1371/journal.pone.0055358> (PMCID: PMC3561278).

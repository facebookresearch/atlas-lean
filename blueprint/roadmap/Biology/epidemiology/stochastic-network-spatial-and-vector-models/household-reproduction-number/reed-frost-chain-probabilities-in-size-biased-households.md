# Reed–Frost chain probabilities in size-biased households

**Model.** Individuals live in households; $k_n$ is the fraction of households of size $n \in \{1, \dots, n_{\max}\}$. Outside the household they mix randomly; inside a household of size $n$, an infective transmits to each susceptible member over its whole infectious period with probability $1 - Q_n$, where $Q_n = e^{-\rho_n}$ is the pairwise escape probability. Within-household spread is approximated by a discrete-generation Reed–Frost chain: if $m_i$ members are infected in generation $i$ and $s_i$ remain susceptible, each susceptible escapes generation $i+1$ independently with probability $Q_n^{m_i}$.

**Proposition 1 (chain probabilities).** Starting from one index case ($m_1 = 1$, $s_1 = n - 1$), the probability of the chain $(m_1, \dots, m_n)$, with $s_{i+1} = s_i - m_{i+1}$ and $m_{i+1} \le s_i$, is

$$\Pr\big(\{m_1, \dots, m_n\} \mid n\big) = \prod_{i = 1}^{n - 1} \binom{s_i}{m_{i+1}} \big(1 - Q_n^{m_i}\big)^{m_{i+1}} \big(Q_n^{m_i}\big)^{s_i - m_{i+1}} .$$

**Proposition 2 (size-biased households).** Under random mixing between households and low prevalence, the size of the household of a newly infected index case has the size-biased law

$$\tilde k_n = \frac{n\, k_n}{\sum_{m} m\, k_m},$$

so the state $X = (n, m_1, \dots, m_n)$ of a newly infected household has law $f(X) = \tilde k_n \Pr(\{m_1, \dots, m_n\} \mid n)$, and the expected number of cases in generation $i$ of a typical infected household is $\mu_i = \sum_X m_i f(X)$, with $\mu_1 = 1$ and mean household outbreak size $\mu = \sum_i \mu_i$.

## Expansion

Given generation $i$, each of the $s_i$ susceptibles is infected in generation $i+1$ with probability $1 - Q_n^{m_i}$ independently, so $m_{i+1}$ is binomial; multiplying the conditional binomial probabilities along the chain gives Proposition 1. A random contact made outside a household lands on a person, not on a household, and the probability that this person belongs to a household of size $n$ is proportional to $n k_n$, which gives Proposition 2. The order of infections does not change the final number infected, so the final household size distribution is exact even though Reed–Frost generations replace real-time dynamics. With the 2001 UK household sizes in the source, the mean household has 2.38 members while the household of the mean individual has 3.06.

## Sources

- C. Fraser, *Estimating individual and household reproduction numbers in an emerging epidemic*, PLoS ONE (2007). <https://doi.org/10.1371/journal.pone.0000758> (PMCID: PMC1950082). Methods, Equations (1)–(12) and (22)–(39).
- D. Ludwig, *Final size distributions for epidemics*, Mathematical Biosciences (1975).

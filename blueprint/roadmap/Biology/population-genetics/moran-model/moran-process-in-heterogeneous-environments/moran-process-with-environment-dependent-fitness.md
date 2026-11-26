# Moran process with environment-dependent fitness

A population of fixed size $N$ occupies $N$ sites, split into $m$ environments; environment $i$ holds $N_i \ge 1$ sites, with $\sum_{i=1}^m N_i = N$. Each individual is of type $A$ (mutant) or $B$ (resident). An $A$ individual on a site of environment $i$ has reproductive rate $a_i > 0$, and a $B$ individual there has rate $b_i > 0$. In each time step one individual is chosen to reproduce with probability proportional to its rate, and its offspring replaces an individual chosen uniformly at random. The offspring takes the rate of its type in the environment of the site it lands on, not that of its parent.

The environment is summarized by the mass functions

$$f_N(a) = \sum_{i:\,a_i = a} \frac{N_i}{N}, \qquad g_N(b) = \sum_{i:\,b_i = b} \frac{N_i}{N},$$

with means $\bar a = \frac1N\sum_i N_i a_i$ and $\bar b = \frac1N\sum_i N_i b_i$. Let $\rho_{e_i,A}$ be the probability that $A$ takes over when a single $A$ starts in environment $i$ and all others are $B$, and let

$$\rho_A^N(f_N, g_N) = \frac1N \sum_{i=1}^m N_i\, \rho_{e_i,A}$$

be the fixation probability of a uniformly placed mutant. $A$ is *neutral* relative to $B$ when $\rho_A^N(f_N,g_N) = \rho_A^N(g_N,f_N)$, that is, when a single $A$ in a $B$ population fixes as often as a single $B$ in an $A$ population.

- **Homogeneous case.** If $a_i = \bar a$ and $b_i = \bar b$ for all $i$, the process is the classical Moran process and $\rho_A^N = \dfrac{1 - \bar b/\bar a}{1 - (\bar b/\bar a)^N}$ for $\bar a \ne \bar b$ (and $1/N$ otherwise); neutrality holds iff $\bar a = \bar b$.
- **Two sites.** For $N = 2$ with one site in each of $m = 2$ environments,

$$\rho_A^2(f,g) = \frac12\left(\frac{a_1}{a_1 + b_2} + \frac{a_2}{a_2 + b_1}\right), \qquad \rho_A^2(g,f) = \frac12\left(\frac{b_1}{b_1 + a_2} + \frac{b_2}{b_2 + a_1}\right),$$

and neutrality holds iff $a_1 a_2 = b_1 b_2$. Equal mean rates, $a_1 + a_2 = b_1 + b_2$, are therefore not the neutrality condition in small populations.

## Depends on

- [Fixation probability of the Moran process](../moran-fixation.md)

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Expansion

With two sites the state changes only when the reproducing individual replaces the other one. Starting from a mutant on site 1 (rate $a_1$) and a resident on site 2 (rate $b_2$), the mutant wins the first effective event with probability $a_1/(a_1 + b_2)$, which ends the process; averaging over the two starting sites gives the formula. Subtracting the two fixation probabilities, $\frac{a_1 - b_2}{a_1 + b_2} + \frac{a_2 - b_1}{a_2 + b_1} = 0$ clears to $2(a_1 a_2 - b_1 b_2) = 0$. Already for $N = 3$ the neutrality condition is a high-degree polynomial identity in the rates (Eq. (2.5) of the source), which is why the large-population limit is the natural regime for analysis.

## Sources

- K. Kaveh, A. McAvoy, M. A. Nowak, "Environmental fitness heterogeneity in the Moran process", Royal Society Open Science (2019), <https://doi.org/10.1098/rsos.181661> (PMC6366185).

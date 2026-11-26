# Random reactive strategies cooperate half the time

Take two strategies $s_1, s_2$ drawn independently and uniformly from the unit square of reactive strategies $(p, q)$, and let $C(s_1, s_2)$ be the long-run probability that $s_1$ cooperates against $s_2$ (see [Cooperation rate between reactive strategies](cooperation-rate-between-reactive-strategies.md)). Then

$$\mathbb{E}\big[C(s_1, s_2)\big] = \frac12 .$$

Consequently, in a population of $N$ players updating by a pairwise comparison (imitation) process with mutation probability $u$, the average cooperation rate equals $1/2$ when $u = 1$: every player then holds a uniformly random reactive strategy, and the population average is the average of pairwise cooperation rates.

## Depends on

- [Cooperation rate between reactive strategies](cooperation-rate-between-reactive-strategies.md)

## Proof sketch

The involution $\bar s = (1 - q, 1 - p)$ preserves the uniform distribution on the square and the reactivity $\varrho = p - q$. For a pair with $|\varrho_1\varrho_2| < 1$ (which holds almost surely),

$$C(\bar s_1, \bar s_2) = \frac{1 - p_1 + \varrho_1(1 - p_2)}{1 - \varrho_1\varrho_2} = \frac{1 - q_1 - \varrho_1 p_2}{1 - \varrho_1\varrho_2} = 1 - C(s_1, s_2),$$

using $1 - p_1 + \varrho_1 = 1 - q_1$ and $p_2 = q_2 + \varrho_2$. Hence $C(s_1,s_2)$ and $1 - C(s_1, s_2)$ have the same distribution, and the mean is $1/2$: cooperation and defection are exchanged by relabelling the two actions. This is the baseline against which the source measures how intermediate mutation rates raise cooperation above the rare-mutation limit (Lemma 2 and Theorem 1 of its Supplementary Note 2).

## Sources

- J. Tkadlec, C. Hilbe, M. A. Nowak, "Mutation enhances cooperation in direct reciprocity", Proceedings of the National Academy of Sciences of the USA (2023), <https://doi.org/10.1073/pnas.2221080120> (PMC10193978).

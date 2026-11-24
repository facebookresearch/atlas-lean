# Lander–Green multipoint likelihood as a hidden Markov chain

In a pedigree with $n$ non-founders, the inheritance pattern at a point $x$ of the genome is described by the binary inheritance vector $v(x) = (p_1, m_1, \dots, p_n, m_n)$, whose coordinates record whether the grandpaternal or grandmaternal allele was transmitted in the paternal and maternal meioses giving rise to each non-founder; there are $2^{2n}$ inheritance vectors (Lander and Green 1987, as described by Kruglyak et al. 1996). Lander and Green treat the inheritance pattern along the genome as a Markov process, with recombination causing transitions between states, observed imperfectly at marker loci, so that the multipoint likelihood and the inheritance distribution given all markers are computed by the forward–backward recursions of a hidden Markov model. The time is linear in the number of markers and exponential in the number of non-founders, so the method suits complete multipoint analysis of pedigrees of moderate size, whereas the Elston–Stewart algorithm scales exponentially with loci and linearly with non-founders. With no interference, meioses recombine independently, so between consecutive loci with recombination fraction $\theta$ the transition probability between inheritance vectors at Hamming distance $d$ is $\theta^d (1 - \theta)^{2n - d}$.

## Depends on

- [The forward algorithm computes the likelihood](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood-eq-sum-forward.md)

## Expansion

1. The model: meioses, inheritance vectors, and the no-interference assumption (independent recombination in disjoint intervals).
2. The Markov property of inheritance vectors along the chromosome and the transition law $\theta^d(1 - \theta)^{2n - d}$, from independence of the $2n$ meioses.
3. The emission probabilities of the marker genotypes given an inheritance vector, summing over founder allele assignments.
4. The likelihood as the forward recursion of this model, and the cost bound.
5. The speedups that use the product structure of the transition matrix and founder-phase symmetry, as separate statements.

## Sources

- L. Kruglyak, M. J. Daly, M. P. Reeve-Daly and E. S. Lander, Parametric and nonparametric linkage analysis: a unified multipoint approach, Am. J. Hum. Genet. 58 (1996), 1347–1363, section on representing and computing inheritance information.
- Lander–Green algorithm, Wikipedia. <https://en.wikipedia.org/wiki/Lander%E2%80%93Green_algorithm>
- Original result: E. S. Lander and P. Green, Construction of multilocus genetic linkage maps in humans, Proc. Natl. Acad. Sci. USA 84 (1987), 2363–2367. <https://doi.org/10.1073/pnas.84.8.2363> The inheritance-vector hidden Markov model follows Kruglyak et al. (1996).

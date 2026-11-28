# Metropolis–Hastings samplers over genealogies

Markov chain Monte Carlo methods for coalescent inference sample a genealogy $G = (\Lambda, T, M)$, a topology $\Lambda$, coalescence times $T$ and mutation parameters $M$, from its posterior $\pi(G) = f(G \mid D)$ given sequence data $D$, with the likelihood $P(D \mid \Lambda, T)$ computed by peeling. In the Metropolis–Hastings scheme presented by Tavaré (2004, Section 9.5, Algorithm 9.1), a new state $G'$ is proposed from a kernel $Q(G \to G')$ and accepted with probability

$$h = \min\Bigl(1, \frac{\pi(G')\,Q(G' \to G)}{\pi(G)\,Q(G \to G')}\Bigr)$$

(equation (9.5.2)). The first such sampler, due to Kuhner, Yamato and Felsenstein (1995), proposes by choosing a target node that is neither a leaf nor the root, erasing the active lineages in its neighbourhood (the target, its child, its parent and the parent's other child), and redrawing them: the topology of the neighbourhood is rearranged and the new times of the target and its parent are drawn from a conditional coalescent distribution given the inactive lineages (Tavaré 2004, Section 9.5 and Fig. 9.1). Kuhner et al. use the resulting genealogies, sampled at one value $\theta_0$, to evaluate a relative likelihood curve at other values of $\theta = 4N_e\mu$ (abstract). Invariance of $\pi$ under such a chain is a property of each move; convergence and mixing need separate arguments.

## Depends on

- [Detailed balance for Metropolis–Hastings](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/markov-chain-monte-carlo/mh-detailed-balance.md)

## Expansion

1. The posterior on genealogies as a density with respect to a reference measure on topologies and times.
2. The neighbourhood rearrangement of Kuhner et al.: its proposal density and that of the reverse move.
3. The Hastings ratio (9.5.2) for this proposal and the resulting reversibility with respect to the posterior.
4. Reweighting genealogies sampled at $\theta_0$ to estimate the likelihood at other $\theta$, and its conditions.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Sections 9.4–9.5, Algorithm 9.1, equation (9.5.2) and Fig. 9.1.
- M. K. Kuhner, J. Yamato and J. Felsenstein, Estimating effective population size and mutation rate from sequence data using Metropolis–Hastings sampling, Genetics 140 (1995), 1421–1430, abstract. <https://doi.org/10.1093/genetics/140.4.1421>

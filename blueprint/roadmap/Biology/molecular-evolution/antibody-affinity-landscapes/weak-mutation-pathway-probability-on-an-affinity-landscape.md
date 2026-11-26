# Weak-mutation pathway probability on an affinity landscape

On the $2^L$ variants between a germline sequence $s_g$ and a somatic sequence $s_s$ (indexed as in the [truncated-order epistasis model](truncated-order-epistasis-model-of-a-combinatorial-landscape.md)), let $y^{ag}_s = -\log_{10} K^{ag}_{D,s}$ be the log affinity of variant $s$ for antigen $ag$. For a step from $s$ to a variant $t$ carrying exactly one more somatic mutation, define the selection coefficient and step probability

$$\sigma = \gamma\, \Delta^{ag}_{s,t} = \gamma\,(y^{ag}_t - y^{ag}_s), \qquad p_{\mathrm{step}}(\sigma, N) = \frac{1 - e^{-\sigma}}{1 - e^{-N\sigma}},$$

with effective population size $N$ and selection strength $\gamma > 0$, and let $P^{ag}$ be the $2^L \times 2^L$ matrix with $P^{ag}_{s,t} = p_{\mathrm{step}}(\gamma \Delta^{ag}_{s,t}, N)$ if $t$ has one more somatic mutation than $s$ and $0$ otherwise (no back mutation). For a sequence of antigen contexts $ag_1, \dots, ag_L$ the total weight of all mutational paths from germline to somatic sequence is

$$\mathcal{P}_{\mathrm{tot}} = \sum_{\text{paths}} \prod_{\text{steps}} p_{\mathrm{step}} = \Bigl[\prod_{i=1}^{L} P^{ag_i}\Bigr]_{s_g, s_s} .$$

In the strong-selection limit $N \to \infty$, $\gamma \to \infty$, the step probability becomes the indicator of $\Delta > 0$ and $\mathcal{P}_{\mathrm{tot}}$ counts the strictly uphill paths.

## Depends on

- [Truncated-order epistasis model of a combinatorial landscape](truncated-order-epistasis-model-of-a-combinatorial-landscape.md)

## Expansion

In the weak-mutation regime the population is monomorphic between fixation events and moves along the hypercube as a Markov chain whose transition weights are fixation probabilities. A path from germline to somatic sequence is an ordering of the $L$ mutations, so there are $L!$ paths, and the $(s_g, s_s)$ entry of the matrix product sums the product of step weights over all of them. As $\sigma \to 0$, $p_{\mathrm{step}} \to 1/N$ (neutral fixation). The rows of $P^{ag}$ are not normalized, so $\mathcal{P}_{\mathrm{tot}}$ compares antigen scenarios (single antigen, sequential antigens, or mixtures) for one antibody but not across antibodies. For CR9114 (16 heavy-chain mutations) the source finds that a sequential scenario, selecting for affinity to each influenza antigen in turn, gives the somatic sequence a much higher total probability than single-antigen or random mixed scenarios, because affinity to diverse antigens is acquired in a nested, epistatic order; for CR6261, whose antigens are more similar, many paths remain accessible under all scenarios.

## Sources

- A. M. Phillips, K. R. Lawrence, A. Moulana, T. Dupic, J. Chang, M. S. Johnson, I. Cvijovic, T. Mora, A. M. Walczak and M. M. Desai, "Binding affinity landscapes constrain the evolution of broadly neutralizing anti-influenza antibodies", *eLife* 10 (2021), e71393, Equations (11)–(14), Materials and methods sections "Selection models" and "Scenario, mutation, and variant probabilities", <https://doi.org/10.7554/eLife.71393> (PMC8476123).

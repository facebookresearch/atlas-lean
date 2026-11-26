# Total-evidence posterior with stratigraphic age ranges

Let $\mathcal{T}$ be a dated sampled tree of extant and fossil taxa (with possible sampled ancestors), $D$ the matrix of molecular and morphological characters, $\bar\theta$ the substitution and clock parameters, $\bar\eta$ the tree-prior (fossilized birth–death) parameters, and $\bar\tau$ the stratigraphic age intervals assigned to the fossils. Assume that, given that a fossilization event happened at time $y$, the probability of assigning a given interval does not depend on $y$ when $y$ lies in that interval and is zero otherwise. Then

$$f(\mathcal{T}, \bar\theta, \bar\eta \mid D, \bar\tau) \propto f(D \mid \mathcal{T}, \bar\theta)\, \delta(\mathcal{T} \in \mathbb{T}_{\bar\tau})\, f(\mathcal{T} \mid \bar\eta)\, f(\bar\eta)\, f(\bar\theta), \tag{1}$$

where $\mathbb{T}_{\bar\tau}$ is the set of trees whose fossil sampling times lie in their assigned intervals.

For a fossil, let $H_1$ be the hypothesis that it is a sampled ancestor and $H_2$ that it is a terminal node. With the conditioned prior

$$f(\mathcal{T}, \bar\eta \mid \bar\tau) \propto \delta(\mathcal{T} \in \mathbb{T}_{\bar\tau})\, f(\mathcal{T} \mid \bar\eta)\, f(\bar\eta), \tag{3}$$

the ages-conditioned Bayes factor

$$\widehat{BF} = \frac{P(H_1 \mid D, \bar\tau)\, P(H_2 \mid \bar\tau)}{P(H_2 \mid D, \bar\tau)\, P(H_1 \mid \bar\tau)}$$

equals the ratio of character-data likelihoods $P(D \mid H_1, \bar\tau) / P(D \mid H_2, \bar\tau)$: it measures the evidence that the characters add, beyond the fossil ages, for the fossil being a sampled ancestor.

## Depends on

- [Fossilized birth–death process and its diversification parameterization](fossilized-birth-death-process-and-its-diversification-parameterization.md)

## Expansion

Equation (1) follows from the full joint density $f(D \mid \mathcal{T}, \bar\theta)\, f(\bar\tau \mid \mathcal{T})\, f(\mathcal{T} \mid \bar\eta)\, f(\bar\eta)\, f(\bar\theta)$ once the range-assignment density is constant on $\mathbb{T}_{\bar\tau}$ and zero off it. The identity for $\widehat{BF}$ is Bayes' rule: $P(H_1 \mid D, \bar\tau)/P(H_2 \mid D, \bar\tau) = [P(D \mid H_1, \bar\tau)/P(D \mid H_2, \bar\tau)] \cdot [P(H_1 \mid \bar\tau)/P(H_2 \mid \bar\tau)]$. It is used because the unconditioned prior probabilities of $H_1$ and $H_2$ are not available. Both posterior and conditioned-prior probabilities are estimated as the fractions of Markov chain Monte Carlo samples (from (1) and from (3)) in which the fossil is a sampled ancestor or a terminal node.

## Sources

- A. Gavryushkina, T. A. Heath, D. T. Ksepka, T. Stadler, D. Welch, A. J. Drummond, "Bayesian total-evidence dating reveals the recent crown radiation of penguins", Systematic Biology (2017), Methods, model overview Eq. (1) and "Bayes Factors", Eq. (3), <https://doi.org/10.1093/sysbio/syw060> (PMC5410945).

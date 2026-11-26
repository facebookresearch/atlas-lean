# General Markov mutation along branches and the law of sample types

Let $Q$ be a rate matrix on a finite set of types with stationary law $\pi$. Given a coalescent genealogy, types evolve along each branch of length $t$ by the transition matrix $e^{t (\theta/2) Q}$, independently on different branches, and the type at the root has law $\pi$. Then the law of the types of the sample is the expectation, over the genealogy, of the product over branches of the transition probabilities along the tree, summed over the types of the internal nodes.

If $Q$ is reversible with respect to $\pi$, two samples whose pair coalescence time is $\tau$ are of the same type with probability

$$\mathbb{P}(\text{identical in state}) = \sum_i \pi_i\, \mathbb{E}\bigl[(e^{\theta \tau Q})_{ii}\bigr].$$

## Depends on

- [Transition function of a rate matrix is stochastic](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition-mem-row-stochastic.md)
- [Detailed balance](../../../Probability/markov-chains/kolmogorov-s-criterion-for-reversibility/detailed-balance.md)

## Expansion

1. The sample type law from the tree-likelihood product.
2. The two-sample formula: the two lineages are joined by a path of length $2\tau$, and reversibility turns the sum over the root type into $\sum_i \pi_i (e^{\theta \tau Q})_{ii}$. Reversibility is needed only for this closed formula.
3. Checks: the parent-independent model is the special case $Q = \mathbf{1} \pi^{\top} - I$, and the Jukes–Cantor model on four states has a closed form.

## Sources

- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://doi.org/10.1007/978-0-387-78168-6> (finite sites).

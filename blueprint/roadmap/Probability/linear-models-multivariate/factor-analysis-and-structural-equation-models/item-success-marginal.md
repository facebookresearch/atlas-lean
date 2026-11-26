# Marginal success probability of a binary item

Let $\pi$ be a probability mass function on a set of ability levels and let $q(\theta)\in[0,1]$ be the conditional probability of success at ability $\theta$. First draw the ability from $\pi$, then draw the binary response from the Bernoulli law with parameter $q(\theta)$. The marginal success probability is the expectation of the indicator that this mixed response is a success.

On a finite ability grid, this expectation is the [weighted average of the success curve](item-success-marginal-eq-sum.md).

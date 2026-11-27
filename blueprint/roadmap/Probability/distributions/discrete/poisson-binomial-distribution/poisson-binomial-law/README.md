# Poisson-binomial distribution

For $m \in \mathbb{N}$, a vector $p = (p_0, \dots, p_{m-1}) \in \mathbb{R}^m$ and $j \in \mathbb{N}$, the Poisson-binomial mass function is

$$\pi_p(j) = \sum_{\substack{A \subseteq \{0, \dots, m-1\} \\ |A| = j}} \prod_{i \in A} p_i \prod_{i \notin A} (1 - p_i).$$

When every $p_i$ lies in $[0, 1]$, it is the law of the number of successes among $m$ independent trials with success probabilities $p_0, \dots, p_{m-1}$; its algebraic identities hold for all real $p$.

## Idea

The set $A$ records which trials succeed, and the product is the probability of exactly that pattern. When all $p_i$ are equal to $q$ this is the binomial law with parameters $m$ and $q$. Adding a trial with success probability $a$ gives the recurrence $\pi_{(a, p)}(j + 1) = a \, \pi_p(j) + (1 - a) \, \pi_p(j + 1)$, which computes the law in $O(m^2)$ steps instead of summing over subsets.

## Statements

- [Poisson-binomial mass function](poisson-binomial-pmf.md)
- [Nonnegativity of the Poisson-binomial mass function](poisson-binomial-pmf-nonneg.md): basic property: nonnegativity
- [Poisson-binomial mass vanishes above the number of trials](poisson-binomial-pmf-eq-zero-of-lt.md): basic property: support
- [Poisson-binomial mass at zero after adding a trial](poisson-binomial-pmf-cons-zero.md): recurrence when a trial is added (mass at zero)
- [First-step recurrence for the Poisson-binomial mass function](poisson-binomial-pmf-cons-succ.md): recurrence when a trial is added
- [Poisson-binomial masses sum to one](sum-poisson-binomial-pmf.md): basic property: normalisation
- [Poisson-binomial law with equal probabilities is binomial](poisson-binomial-pmf-const.md): special case: equal probabilities give the binomial
- [Distribution of a sum of independent Bernoulli variables](bernoulli-sum-pmf.md): characterisation: law of a sum of independent Bernoulli variables
- [Binomial distribution of a sum of i.i.d. Bernoulli variables](bernoulli-sum-pmf-iid.md): i.i.d. special case: binomial
- [Upper tail of the Poisson-binomial law](poisson-binomial-tail.md): definition of the upper tail
- [Peeling off the lowest term of the Poisson-binomial tail](poisson-binomial-tail-eq-add.md): recurrence for the tail
- [Poisson-binomial tail after adding a trial](poisson-binomial-tail-cons-succ.md): recurrence for the tail when a trial is added
- [Tail of a sum of independent Bernoulli variables is Poisson-binomial](measure-le-sum-eq-poisson-binomial-tail.md): characterisation: tails of sums of independent Bernoulli variables
- [Bernoulli random variable](is-bernoulli-rv.md): definition of Bernoulli random variables used by the characterisation
- [Bernoulli parameters are nonnegative](nonneg.md): basic fact about Bernoulli parameters
- [Bernoulli parameters are at most one](le-one.md): basic fact about Bernoulli parameters
- [Law of a Bernoulli random variable](has-law.md): law of a Bernoulli random variable
- [Probability that a Bernoulli variable equals one](measure-one.md): basic fact about Bernoulli random variables
- [Probability that a Bernoulli variable equals zero](measure-zero.md): basic fact about Bernoulli random variables

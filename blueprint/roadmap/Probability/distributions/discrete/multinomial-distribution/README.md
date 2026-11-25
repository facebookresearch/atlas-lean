# Multinomial distribution

Let $\iota$ be a finite set, $N \in \mathbb{N}$ and $p$ a probability vector on $\iota$ ($p_i \ge 0$ for every $i$ and $\sum_i p_i = 1$). The multinomial distribution of $N$ throws with cell probabilities $p$ is the probability distribution on count vectors $x \in \mathbb{N}^\iota$ with mass

$$M_N(p; x) = \frac{N!}{\prod_i x_i!} \prod_i p_i^{x_i}$$

when $\sum_i x_i = N$, and mass $0$ otherwise.

## Idea

Throw $N$ balls independently into the cells of $\iota$, each landing in cell $i$ with probability $p_i$, and record how many land in each cell. A given sequence of landings with counts $x$ has probability $\prod_i p_i^{x_i}$, and the multinomial coefficient counts these sequences; the multinomial theorem $\bigl(\sum_i p_i\bigr)^N = \sum_x M_N(p; x)$ shows that the masses sum to $1$. With two cells this is the binomial law. Each count $X_i$ has mean $N p_i$ and variance $N p_i (1 - p_i)$, and two different counts have covariance $-N p_i p_j$: with the total fixed, the cells compete. The law also arises from independent Poisson counts conditioned on their total, with cell probabilities proportional to the Poisson means.

## Statements

- [Multinomial distribution](multinomial.md)
- [Multinomial mass function](multinomial-real.md): definition of the mass function used in the main definition
- [Mass of the multinomial distribution at a count vector](multinomial-apply.md): formula for the point masses
- [Nonnegativity of the multinomial mass function](multinomial-real-nonneg.md): basic property: nonnegativity
- [Multinomial mass vanishes off the simplex](multinomial-real-of-sum-ne.md): basic property: support on the simplex
- [Support of the multinomial mass lies in the antidiagonal](multinomial-real-of-not-mem.md): basic property: support
- [Multinomial mass formula on the simplex](multinomial-real-eq-factorial-div.md): factorial formula for the mass
- [Multinomial theorem](sum-multinomial-real-eq-pow.md): multinomial theorem, used for normalisation
- [Normalization of the multinomial distribution](sum-multinomial-real.md): basic property: normalisation
- [Mean of the multinomial mass function, polynomial form](sum-mul-multinomial-real-eq.md): polynomial identity used for the mean
- [Mean of the multinomial distribution](sum-mul-multinomial-real.md): basic property: the means $N p_i$
- [Second factorial moment, polynomial form](sum-mul-sub-one-multinomial-real-eq.md): polynomial identity used for the factorial moments
- [Second factorial moment of the multinomial distribution](sum-mul-sub-one-multinomial-real.md): second factorial moments, used for the covariance
- [Mixed second moment, polynomial form](sum-mul-mul-multinomial-real-of-ne-eq.md): polynomial identity used for the mixed moments
- [Mixed second moment of the multinomial distribution](sum-mul-mul-multinomial-real-of-ne.md): mixed second moments, used for the covariance
- [Covariance of the multinomial distribution](sum-covariance-multinomial-real.md): basic property: the covariance matrix
- [Poisson conditioning](cond-measure-real-eq-multinomial-real.md): characterisation: independent Poisson counts given their total
- [Poisson conditioning, two cells](cond-measure-real-eq-binomial.md): two-cell special case
- [Binomial law of a Poisson count given the total](has-law-cond-binomial.md): the two-cell case, stated as a conditional law

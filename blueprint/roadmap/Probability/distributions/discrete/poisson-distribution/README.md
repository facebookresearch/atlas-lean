# Sums of independent Poisson variables

Let $(K_i)_{i \in I}$ be mutually independent $\mathbb{N}$-valued random variables on a probability space with $K_i \sim \operatorname{Poisson}(\lambda_i)$, $\lambda_i \ge 0$, for every $i \in I$, where $\operatorname{Poisson}(\lambda)$ has mass $e^{-\lambda} \lambda^k / k!$ at $k$. Then for every finite set $s \subseteq I$,

$$\sum_{i \in s} K_i \sim \operatorname{Poisson}\Bigl(\sum_{i \in s} \lambda_i\Bigr),$$

where for $s = \emptyset$ both sides are the point mass at $0$.

## Idea

The sum of two independent Poisson variables is Poisson: convolving the masses and applying the binomial theorem gives

$$\sum_{k=0}^{n} e^{-\lambda} \frac{\lambda^k}{k!} \, e^{-\lambda'} \frac{\lambda'^{\,n-k}}{(n-k)!} = e^{-(\lambda + \lambda')} \frac{(\lambda + \lambda')^n}{n!}.$$

Induction on the finite set $s$ extends this closure from two summands to finitely many. Intuitively, a Poisson variable counts rare events that occur independently, and merging independent streams of such events gives another such stream whose rate is the sum of the rates. In generating-function terms, $\mathbb{E} z^{K_i} = e^{\lambda_i (z - 1)}$, and the product of these functions over $i \in s$ is $e^{(\sum_i \lambda_i)(z - 1)}$.

## Statements

- [Finite sums of independent Poisson variables are Poisson](has-law-sum-poisson-measure.md)

## Related topics

- [Indian buffet process](../../../bayesian-statistics/indian-buffet-process/README.md): independent Poisson counts of feature histories, whose total number of features is Poisson by this closure.

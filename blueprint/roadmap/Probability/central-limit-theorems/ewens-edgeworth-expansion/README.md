# Local Edgeworth expansion for the Ewens distribution

Let $r \ge 0$ be an integer and let $L \subseteq (0, \infty)$ be compact. For $\theta > 0$ and integers
$n \ge 2$ and $1 \le k \le n$, let $s(n, k)$ be the unsigned Stirling number of the first kind (the
number of permutations of $n$ elements with exactly $k$ cycles), let

$$p_n(k; \theta) = \frac{\theta^k s(n, k)}{\theta (\theta + 1) \cdots (\theta + n - 1)}$$

be the probability that a random permutation of $n$ elements with the Ewens distribution of parameter
$\theta$ has exactly $k$ cycles, and let $x_n(k; \theta) = (k - \theta \log n)/\sqrt{\theta \log n}$.
Then there are functions $H_0, H_1, \dots : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ such that, as
$n \to \infty$,

$$(\log n)^{(r+1)/2} \left| p_n(k; \theta) - \frac{e^{-x^2/2}}{\sqrt{2 \pi \theta \log n}} \sum_{j=0}^{r} \frac{H_j(x, \theta)}{(\theta \log n)^{j/2}} \right| \to 0, \qquad x = x_n(k; \theta),$$

uniformly in $\theta \in L$ and $1 \le k \le n$. The functions $H_j$ are only asserted to exist; they
may depend on $r$ and $L$, and they need not be polynomials.

## Idea

Under the Ewens distribution with parameter $\theta$, a permutation of $n$ elements has probability
proportional to $\theta$ raised to its number of cycles; $\theta = 1$ is the uniform distribution. The
number of cycles $K_n$ has the law of a sum of independent Bernoulli variables with success
probabilities $\theta/(\theta + i - 1)$, $1 \le i \le n$, so its mean and variance are both close to
$\theta \log n$, and $K_n$ is asymptotically normal. The statement refines the corresponding local
limit theorem: the point probabilities $p_n(k; \theta)$ equal the normal density at $x$ times a
correction series in powers of $(\theta \log n)^{-1/2}$, an Edgeworth expansion, with an error that is
$o((\log n)^{-(r+1)/2})$ uniformly in $k$ and in $\theta$ on compact sets. The statement asserts only
that suitable correction functions exist; it does not specify them.

## Statements

- [Local Edgeworth expansion for the Ewens distribution](stirling-edgeworth-expansion.md)

## Sources

- Z. Kabluchko, A. Marynych and H. Sulzbach, "Mode and Edgeworth expansion for the Ewens distribution
  and the Stirling numbers", Journal of Integer Sequences (2016).

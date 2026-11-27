# Hypergeometric distribution

Let $N, K, n \in \mathbb{N}$ with $K \le N$ and $n \le N$. The hypergeometric distribution is the probability distribution on $\mathbb{N}$ that gives $k \le n$ the mass

$$h(N, K, n, k) = \frac{\binom{K}{k} \binom{N - K}{n - k}}{\binom{N}{n}}$$

and every $k > n$ the mass $0$. It is the law of the number of marked items in $n$ draws without replacement from $N$ items of which $K$ are marked.

## Idea

All $\binom{N}{n}$ sets of $n$ items are equally likely, and the numerator counts those with exactly $k$ marked items: choose $k$ of the $K$ marked items and $n - k$ of the $N - K$ others. The mass vanishes when $k$ exceeds $n$ or $K$, and Vandermonde's identity $\sum_k \binom{K}{k} \binom{N-K}{n-k} = \binom{N}{n}$ makes the masses sum to $1$. For $N > 0$ the mean is $nK/N$, the same as for $n$ draws with replacement, which give a binomial count with success probability $K/N$; drawing without replacement changes the spread, not the mean. In a lottery that draws $6$ numbers out of $49$, the number of your $6$ numbers that are drawn is hypergeometric with $N = 49$ and $K = n = 6$.

## Statements

- [Hypergeometric distribution](hypergeometric.md)
- [Hypergeometric mass function](hypergeometric-real.md): definition of the mass function used in the main definition
- [Point masses of the hypergeometric distribution](hypergeometric-apply.md): formula for the point masses
- [Nonnegativity of the hypergeometric mass function](hypergeometric-real-nonneg.md): basic property: nonnegativity
- [Hypergeometric mass vanishes above the number of draws](hypergeometric-real-of-lt.md): basic property: support (number of draws)
- [Hypergeometric mass vanishes above the number of marked items](hypergeometric-real-of-lt-2.md): basic property: support (number of marked items)
- [Normalization of the hypergeometric distribution](sum-hypergeometric-real.md): basic property: normalisation (Vandermonde)
- [Mean of the hypergeometric distribution](sum-mul-hypergeometric-real.md): basic property: the mean $nK/N$
- [Second factorial moment of the hypergeometric distribution](sum-mul-sub-one-mul-hypergeometric-real.md): basic property: the second factorial moment
- [Variance of the hypergeometric distribution](sum-sq-sub-mean-mul-hypergeometric-real.md): basic property: the variance
- [Marked items in a uniform random sample](marked-items-in-a-uniform-random-sample.md): a model: the count of marked items in a uniformly random n-subset has this law

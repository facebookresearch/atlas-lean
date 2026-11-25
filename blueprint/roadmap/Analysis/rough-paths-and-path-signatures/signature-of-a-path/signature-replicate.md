# Signature along a repeated letter

Let the component $v^i$ of the velocity of $X$ be continuous. For every $k$ and reals $s, t$, the
iterated integral along the word $i i \cdots i$ with $k$ letters is

$$S(X)^{i \cdots i}_{s,t} = \frac{\big(X^i_t - X^i_s\big)^k}{k!}, \qquad X^i_t - X^i_s = \int_s^t v^i(u)\,du .$$

In particular the signature of a one-dimensional path depends only on its increment, and for
$X_t = t$ it is $\big(1, t - s, (t-s)^2/2!, (t-s)^3/3!, \dots\big)$.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Example 1.6 ("the above expression of the signature remains true for any
  path").

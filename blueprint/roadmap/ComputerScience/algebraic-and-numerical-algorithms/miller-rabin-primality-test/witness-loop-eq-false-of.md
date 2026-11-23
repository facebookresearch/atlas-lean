# Converse for the squaring loop

Let $n > 2$ and let $x < n$. If $x = 1$, or if $x^{2^i} \equiv -1 \pmod n$ (that is,
$x^{2^i} \bmod n = n - 1$) for some $i < k$, then the [squaring loop](witness-loop.md) with $k$
squarings started at $x$ reports no witness. Together with
[When the squaring loop finds no witness](witness-loop-eq-false-imp.md) this characterises the
loop's *no witness* answer.

The hypothesis $n > 2$ is needed: for $n = 2$ the values $1$ and $n - 1$ coincide.

## Sources

- M. O. Rabin, *Probabilistic algorithm for testing primality*, Journal of Number Theory 12 (1980), 128–138, note added on 10 May 1978 (p. 137): the squaring chain and the observation that
  $x_{i-1} = n - 1$ is followed by $x_i = 1$.

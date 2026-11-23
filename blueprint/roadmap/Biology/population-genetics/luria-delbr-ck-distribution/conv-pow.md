# Convolution power of a sequence on the naturals

For a real sequence $p$ on the natural numbers, its $k$-fold convolution powers $p^{*k}$ are defined recursively: $p^{*0}(n) = 1$ if $n = 0$ and $0$ otherwise, and

$$p^{*(k+1)}(n) = \sum_{i=0}^{n} p(i)\, p^{*k}(n - i).$$

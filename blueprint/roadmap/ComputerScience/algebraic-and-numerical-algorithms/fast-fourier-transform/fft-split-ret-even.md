# The FFT split extracts the even-indexed entries

Let $R$ be a type, $m$ a natural number
and $x = (x_0, \dots, x_{2m-1})$ a vector of length $2m$ over $R$. For every $k < m$, entry $k$
of the first (even) vector returned by the FFT split of $x$ is $x_{2k}$.

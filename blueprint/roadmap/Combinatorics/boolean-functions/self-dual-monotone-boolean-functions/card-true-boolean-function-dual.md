# Weight of the dual of a Boolean function

For every $n$ and every Boolean function $b$ on $\{0,1\}^n$, monotone or not, $\ell(b^*) = 2^n - \ell(b)$. Here $\ell(b)$ is the number of inputs $x \in \{0,1\}^n$ with $b(x) = 1$, and $b^*(x) = \lnot b(\bar x)$ is the dual of $b$, where $\bar x$ is the coordinatewise complement of $x$. The subtraction is exact because $\ell(b) \le 2^n$.

The corresponding part of [Lemma 8](monotone-boolean-function-weight-dual.md) assumes that $b$ is monotone; this statement does not.

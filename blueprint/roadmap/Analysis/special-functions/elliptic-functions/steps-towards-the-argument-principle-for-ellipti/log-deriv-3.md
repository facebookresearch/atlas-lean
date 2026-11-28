# The logarithmic derivative of an elliptic function is elliptic

Let $L$ be a period pair
and let $f$ be an elliptic function for $L$. Then its logarithmic derivative
$f'/f$ (Mathlib's `logDeriv f`, with $f'(z)/f(z) = 0$ where $f(z) = 0$) is an elliptic function for
$L$: it is meromorphic on $\mathbb{C}$ and $(f'/f)(z + \omega) = (f'/f)(z)$ for every period
$\omega$ of $L$.

## Sources

- Milne, *Elliptic Curves*, 2nd ed., Chapter III, proof of Proposition 2.1, p. 87: "For (b) one applies the residue theorem to $f'/f$, noting that this is again doubly periodic". The source assumes that $f$ is not identically zero as a meromorphic function, that is, $f$ vanishes on no punctured neighbourhood of any point (equivalently, its meromorphic order is finite at every point). The proof does not use this, and the hypothesis is dropped: for instance, for $f = 0$ the logarithmic derivative is the elliptic function $0$.

# Inverting the Rabin function extracts square roots

For all $n$, $d$ and $x \in \mathbb{Z}/n\mathbb{Z}$, the [Rabin function](rabin-function.md) satisfies

$$E_{n,2d}(x) = (x + d)^2 - d^2.$$

So an algorithm that inverts $E_{n,2d}$ (returns one preimage of each value in its range) also
extracts square roots modulo $n$: a preimage $x$ of $m - d^2$ gives the square root $x + d$ of $m$.
Rabin uses this with $n$ odd, where every $b$ is of the form $2d$ modulo $n$.

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 4, pp. 11–12.

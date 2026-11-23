# The Rabin function

For natural numbers $n$ and $b$, the Rabin function is $E_{n,b}(x) = x(x + b)$ for
$x \in \mathbb{Z}/n\mathbb{Z}$. In Rabin's scheme the public key is $(n, b)$ with $n = pq$ a product
of two large primes and $0 \le b < n$; the primes $p$, $q$ are the private key. Computing
$E_{n,b}$ needs one addition and one multiplication modulo $n$, and no knowledge of $p$ and $q$.
The function is four-to-one on most inputs, where the RSA function is one-to-one.

The definition allows any $n$ and $b$; the hypotheses on $n$ are assumptions of the results about it.

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 1, Definition 1.

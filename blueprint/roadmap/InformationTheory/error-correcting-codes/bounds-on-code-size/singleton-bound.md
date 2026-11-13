# Singleton bound

Let $\alpha$ be a nonempty finite alphabet with $q$ letters, and let $n$
and $d$ be natural numbers with $1 \le d \le n$. If $C$ is a set of words of length $n$ over
$\alpha$ in which any two distinct words are at Hamming distance at least $d$, then $C$ has at
most $q^{n - d + 1}$ elements.

The proof punctures the code to its first $n - d + 1$ coordinates: two codewords agreeing on all
retained coordinates can differ in at most the $d - 1$ deleted coordinates, contradicting the
minimum-distance hypothesis, so puncturing is injective on the code and the bound follows by
counting the punctured words.

## Sources

- R. C. Singleton, "Maximum distance q-nary codes", IEEE Transactions on Information Theory 10(2) (1964), 116–118, DOI 10.1109/TIT.1964.1053661.

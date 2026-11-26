# Succinctness of Kilian's protocol

In Kilian's argument with security parameter $n$, an $n$-bit hash key, $k = n$ repetitions of a PCP verifier using $r(x)$ random bits and at most $q$ queries per random string, and a hash with $n$-bit digests over a table of $N \le 2^{r(x)}\cdot q$ positions, the honest prover's response consists of at most $k q$ openings, each of one bit and an authentication path of $\lceil \log_2 N\rceil$ digests. The total honest communication is therefore at most

$$
n + n + k\, r(x) + k\, q\,(1 + n\lceil\log_2 N\rceil)
$$

bits, which for a verifier with $r(x) \le c(\log_2|x| + 1)$ random bits is polynomial in $n$ and polylogarithmic in $|x|$. Moreover every accepted transcript has at most the length displayed above, and verification reads only that many leading bits of a raw prover message, so the verifier runs in time polynomial in $n$ and $\log |x|$ on arbitrary (unframed or oversized) prover messages.

## Proof sketch

Count the bits of the key, the root, the PCP randomness and the openings; accepted transcripts are bounded because each opened path has fixed length.

## Depends on

- [Succinct arguments from probabilistically checkable proofs](../succinct-arguments-from-probabilistically.md)

## Sources

- Joe Kilian, "A Note on Efficient Zero-Knowledge Proofs and Arguments (Extended Abstract)", Proceedings of the Twenty-Fourth Annual ACM Symposium on Theory of Computing, 1992.
- Boaz Barak and Oded Goldreich, "Universal Arguments and their Applications", Electronic Colloquium on Computational Complexity, 2001.

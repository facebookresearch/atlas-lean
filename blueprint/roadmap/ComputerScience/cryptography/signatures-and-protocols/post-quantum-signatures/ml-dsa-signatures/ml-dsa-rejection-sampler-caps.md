# Exhaustion probability of ML-DSA's matrix rejection sampler

In FIPS 204, RejNTTPoly (Algorithm 30) squeezes three bytes at a time from a SHAKE128 stream and passes them to CoeffFromThreeBytes (Algorithm 14), which clears the top bit of the third byte and accepts the resulting 23-bit value if it is below $q = 8380417$; the sampled NTT vector consists of the first $256$ accepted coefficients in stream order, and ExpandA (Algorithm 32) samples each of the $k\ell$ matrix entries with RejNTTPoly from its own seed. When the XOF output is modeled as uniformly random bytes, the number of coefficients accepted in $n$ squeezes is $\mathrm{Binomial}(n, 2^{-23}q)$, and a RejNTTPoly capped at $298$ iterations ($894$ XOF bytes, the minimum caps allowed by FIPS 204, Appendix C, Table 3) fails, accepting fewer than $256$ coefficients, with probability less than $2^{-256}$ (Appendix C).

## Proof sketch

A triple is rejected only if its 23-bit value is at least $q > 2^{23} - 2^{13}$, which forces the low seven bits of the third byte to be all ones and the middle byte to be at least $224$, an event of probability at most $2^{-10}$; failure within the cap needs at least $298 - 255 = 43$ rejected triples, so its probability is at most $\binom{298}{43} 2^{-430} < 2^{-256}$. A union bound over the $k\ell$ entries bounds the probability that a capped ExpandA fails by $k\ell$ times this bound.

## Depends on

- [The ML-DSA signature scheme](ml-dsa-scheme.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024, Algorithms 14, 30 and 32, Appendix C and Table 3.

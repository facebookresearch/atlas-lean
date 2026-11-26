# Exhaustion probability of ML-DSA's matrix rejection sampler

In FIPS 204, RejNTTPoly reads three bytes at a time from a SHAKE128 stream, masks the top bit of the third byte, and accepts the resulting 23-bit value if it is below $q = 8380417$; the sampled NTT vector consists of the first $256$ accepted coefficients in stream order, and the sampler exhausts exactly when fewer than $256$ are accepted. With the cap of $894$ bytes ($298$ triples) from FIPS 204, Appendix C, Table 3, exhaustion requires at least $43$ rejected triples, each of which has middle byte at least $224$ and low seven bits of the third byte all ones; for uniformly random bytes the exhaustion probability is below $2^{-256}$ (as Appendix C states), and a union bound over the $k\ell$ matrix entries bounds the probability that ExpandA exhausts. Moreover, exchanging the first accepted coefficients of a byte row with an external polynomial is an involution that preserves the ignored bits, the rejected triples and exhaustion, which lets the matrix be reprogrammed to a given uniform matrix in security proofs.

## Proof sketch

A triple is rejected only if its 23-bit value is at least $q > 2^{23} - 2^{13}$, which forces the stated byte patterns; count the placements of $43$ rejections among $298$ triples and multiply by the probability of each pattern.

## Depends on

- [The ML-DSA signature scheme](ml-dsa-scheme.md)

## Sources

- National Institute of Standards and Technology, "Module-Lattice-Based Digital Signature Standard", National Institute of Standards and Technology, 2024.

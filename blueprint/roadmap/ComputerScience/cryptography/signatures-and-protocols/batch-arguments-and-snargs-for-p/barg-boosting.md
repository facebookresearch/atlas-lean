# Boosting batch arguments to proof size independent of the batch size

If there is a somewhere extractable BARG for NP whose proofs have size $k^{1-\epsilon}\cdot\mathrm{poly}(\lambda,|C|)$ for $k$ instances and some constant $\epsilon>0$, then (assuming additionally a somewhere extractable hash, which follows from the same assumptions in known instantiations) there is a somewhere extractable BARG for NP with proof size $\mathrm{poly}(\lambda,|C|)$, independent of $k$, and a RAM delegation scheme (SNARG for RAM computations) with proof size $\mathrm{poly}(\lambda,\log T)$.

## Proof sketch

Recursively batch: split the instances into groups, prove each group with the weak BARG, and prove the validity of the group proofs as a new batch whose instances are hashed with a somewhere extractable hash; sublinear proof size makes each level shrink the total size. Somewhere extractability propagates through the levels via the hidden-index hashes.

## Depends on

- [Batch arguments for NP from LWE](cjj-barg-from-lwe.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Proof depends on

- [Batch arguments for NP from LWE](cjj-barg-from-lwe.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Sources

- Yael Tauman Kalai, Alex Lombardi, Vinod Vaikuntanathan, Daniel Wichs, "Boosting Batch Arguments and RAM Delegation", STOC (2023).

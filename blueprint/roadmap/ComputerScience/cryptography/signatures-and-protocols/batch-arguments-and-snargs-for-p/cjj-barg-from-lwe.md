# Batch arguments for NP from LWE

Assuming polynomial hardness of LWE, there is a somewhere extractable non-interactive batch argument for circuit satisfiability with $k$ instances whose proof size and verification time (beyond reading the instances) are $\mathrm{poly}(\lambda,|C|,\log k)$, with a common reference string of the same size.

## Proof sketch

Construct a BARG for an index language via correlation-intractable Fiat–Shamir applied to a batch protocol in which the prover commits to all witnesses with a somewhere extractable hash and answers a single combined consistency test; the extraction trapdoor lets the reduction recover the witness at the hidden index, and CI from LWE makes the challenge non-adaptively sound. Instances are compressed by hashing them into the reference structure.

## Depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Correlation intractability and NIZK for NP from LWE](ci-from-lwe.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Proof depends on

- [Correlation intractability and NIZK for NP from LWE](ci-from-lwe.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)

## Sources

- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "Non-Interactive Batch Arguments for NP from Standard Assumptions", CRYPTO (2021), IACR ePrint 2021/807.
- Arka Rai Choudhuri, Abhishek Jain, Zhengzhong Jin, "SNARGs for P from LWE", FOCS (2021), IACR ePrint 2021/808.

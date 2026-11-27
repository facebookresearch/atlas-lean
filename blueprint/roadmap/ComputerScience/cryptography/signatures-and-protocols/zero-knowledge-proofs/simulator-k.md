# The rewinding simulator truncated after $k$ attempts

Run up to $k$ independent [rewinding attempts](attempt-dist.md) and output the simulated view of the
first successful one, or a failure symbol if all $k$ attempts fail. Goldwasser, Micali and Rackoff's
simulator repeats until success ("DO FOREVER") and runs in expected polynomial time; the truncation
trades perfect simulation for a failure probability.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Theorem 1.
- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, proof of Theorem 2.

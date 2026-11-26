# Capped block rejection sampling from fair bits

Let $\mu$ be a target distribution on a finite set $S$ with dyadic weights relative to blocks of $k$ fair bits: there is a map from a subset $A \subseteq \{0,1\}^k$ onto $S$ whose fibers have sizes proportional to $\mu$. The procedure that draws up to $T$ independent $k$-bit blocks, returns the image of the first block in $A$, and otherwise returns a fixed fallback element, has output distribution within statistical distance $(1 - |A|/2^k)^T$ of $\mu$. In particular a uniform element of $\{0, \dots, m-1\}$ is sampled from $\lceil\log_2 m\rceil$-bit blocks with distance at most $2^{-T}$.

## Proof sketch

Conditioned on acceptance at some trial the output has law exactly $\mu$; all $T$ trials reject with probability $(1 - |A|/2^k)^T$, and for uniform sampling $|A|/2^k = m/2^{\lceil\log_2 m\rceil} \ge 1/2$.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [Repeated simulation attempts with independent success coins](../../cryptography/security-games/computational-indistinguishability-of-ensembles/repeated-attempts-with-independent-success-coins.md)

## Sources

- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd edition, Addison-Wesley, 1997.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.

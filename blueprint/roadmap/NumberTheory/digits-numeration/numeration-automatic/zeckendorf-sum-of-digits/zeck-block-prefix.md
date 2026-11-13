# Block prefixes of a natural number

The blocks of $r \in \mathbb{N}$ are the maximal runs
of Zeckendorf indices of $r$ in which consecutive indices differ by exactly $2$, listed from the
unit digit. For $i \in \mathbb{N}$, the block prefix $r[i]$ is the sum of the Fibonacci numbers
$F_j$ over the indices $j$ in the first $i$ blocks of $r$, or in all blocks when $i$ exceeds the
number $\rho(r)$ of blocks. Thus $r[0] = 0$ and $r[i] = r$ for $i \ge \rho(r)$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Section 7.1 (definition of `r[i]`).

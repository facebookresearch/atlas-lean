# Blocks of a Zeckendorf representation

Let $r \in \mathbb{N}$ have Zeckendorf
representation $r = F_{i_1} + \dots + F_{i_s}$ with $i_1 > \dots > i_s \ge 2$ (Fibonacci numbers
with $F_1 = F_2 = 1$). The blocks of $r$ are the maximal runs of successive terms of the list
$i_1, \dots, i_s$ in which each index is exactly $2$ less than the one before it (the maximal
factors $(10)^m$ of the expansion, a final $1$ at the unit position counting as $10$). The blocks
are listed from the unit digit, so the first block contains $i_s$ and the last contains $i_1$, and
each block lists its indices in decreasing order. The number of blocks of $r$ is $\rho(r)$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Definition 2 (blocks) and Section 7.1.

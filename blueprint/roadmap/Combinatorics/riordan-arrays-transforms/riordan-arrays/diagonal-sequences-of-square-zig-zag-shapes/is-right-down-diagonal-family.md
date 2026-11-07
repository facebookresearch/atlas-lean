# Right-down diagonal families of order $k$

For a natural number $k$, a family
$(A_j)_{0 \le j \le k+1}$ of integer sequences $A_j : \mathbb{N} \to \mathbb{Z}$ is a family of
right-down diagonal sequences of order $k$ when $k \ge 1$ and, for every $j$ and every natural
number $n \ge \lfloor k/2 \rfloor + 1$,

$$A_j(n) = \sum_{i=0}^{\lfloor k/2 \rfloor} c_k(i)\, A_j(n-1-i),$$

where $c_k(i) = (-1)^i \binom{k+1-i}{i+1}$ is the right-down diagonal coefficient.

## Sources

- László Németh and László Szalay, *Sequences Involving Square Zig-Zag Shapes*, Journal of Integer Sequences 24 (2021), Article 21.5.2. Stable source identifiers: concept `jis_sem_81073f165e7dac1ef20a1a7a`, statement `jis_0034612dbd4f4faf5fca455c`.

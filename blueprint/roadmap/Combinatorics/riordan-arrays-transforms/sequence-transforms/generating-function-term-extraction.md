# Recovering a sequence term from its generating function

Let $t_0, t_1, t_2, \dots$ be
natural numbers and let $c$, $m$, $N$ be natural numbers with $c \ge 2$ and $2 \le m \le N$.
Suppose that the real series $\sum_{k \ge 0} t_k \, (c^{-N})^k$ is summable and that
$t_j < c^{j-2}$ for every $j \ge m$. Then

$$t_N = \Bigl\lfloor c^{N^2} \sum_{k \ge 0} t_k \, (c^{-N})^k \Bigr\rfloor \bmod c^N.$$

## Sources

- Mihai Prunescu and Joseph M. Shunia, "On Modular Representations of C-Recursive Integer Sequences", Journal of Integer Sequences 28 (2025), Article 25.5.3, Theorem 2, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Prunescu/prunescu3.pdf>. The paper attributes the result to Prunescu and Sauras-Altuzarra.

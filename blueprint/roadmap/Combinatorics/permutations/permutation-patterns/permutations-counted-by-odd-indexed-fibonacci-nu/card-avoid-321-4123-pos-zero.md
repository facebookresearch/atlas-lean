# Position of the smallest entry in $(321, 4123)$-avoiding permutations

For a natural
number $m$, write $S_m(321, 4123)$ for the set of permutations of $\{0, 1, \dots, m-1\}$ that
avoid both patterns $321$ and $4123$, that is, contain neither of them. Let $n \ge 1$ and let
$j$ be a position with $j + 1 < n$. Then the number of permutations $\sigma \in S_n(321, 4123)$
with $\sigma(j) = 0$ equals $(j + 1) \cdot |S_{n-j-1}(321, 4123)|$.

In the source, positions and values start at $1$: with $k = j + 1$, the number of such
permutations with $\sigma(k) = 1$ is $k \cdot |S_{n-k}(321, 4123)|$ for $1 \le k < n$.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", Proposition 2.

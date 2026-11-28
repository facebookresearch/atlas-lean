# Counting permutations avoiding 321 and the vincular pattern 2143

For every natural number $n \ge 1$, the number of permutations of $\{0, \dots, n-1\}$ that avoid the classical pattern $321$ and avoid the vincular pattern $2143$ (positions $i, i+1, j, k$ with $i + 1 < j < k$ and $\sigma(i+1) < \sigma(i) < \sigma(k) < \sigma(j)$) is the Fibonacci number $F_{2n-1}$.

A permutation $\sigma$ of $\{0, \dots, n-1\}$ contains a pattern $\pi$ of length $k$ (written with values $0, \dots, k-1$) when there are positions $e_0 < \dots < e_{k-1}$ with $\sigma(e_i) < \sigma(e_j) \iff \pi(i) < \pi(j)$ for all $i, j$; it avoids $\pi$ when it does not contain it. $F_m$ is the Fibonacci number with $F_0 = 0$, $F_1 = 1$, and the subtraction in the index is natural-number subtraction.

## Sources

- Juan B. Gil, Felix H. Xu, and William Y. Zhu, "Odd-Indexed Fibonacci Numbers via Pattern-Avoiding Permutations", *INTEGERS* 25 (2025), Article A79, Proposition 4.

# Weighted lower bound for the squarefree totient sum

For every natural number $z \ge 100$,
$\log z + 36/100 < \sum_{q=1}^{z} (1 + q/z)^{-1} \, \mu(q)^2 / \varphi(q)$, where $\mu$ is the
Möbius function and $\varphi$ is Euler's totient function.

## Sources

- Montgomery–Vaughan, *The large sieve* (1973), Lemma 8, lines 658–714. The proof uses Abel summation, `moebiusSq_div_totient_sum_gt_log`, and the paper's explicit correction from the terms `q ≤ 5`.

# Update-only cell-probe lower bounds for succinct dictionaries with large values

For every $\alpha_V > 0$, $\kappa_V \ge \alpha_V$ and $c_w \ge 0$ (and $c_R \ge 0$ for the iterated-log forms) there are constants $c > 0$ and $n_0$ such that for all $U, V, n$ with $n \ge n_0$, $3n \le U$ and $U^{2 + \alpha_V} \le V n^2 \le U^{2 + \kappa_V}$, every deterministic step-indexed or zero-error randomized cell-probe scheme with words of $w \le c_w(\log_2 U + \log_2 V)$ bits implementing the dynamic dictionary exactly on admissible histories of length at most $3n+1$ satisfies, on the insert–delete distribution ($3n$ updates, no query time charged):

1. if $Sw \le \mathrm{OPT}(U,V,n) + c_R n \max(\log^{(k)} n, 1)$ with $1 \le k \le \log^* n$, the expected number of probes is at least $c\, n k$;
2. if $Sw \le \mathrm{OPT}(U,V,n) + R$ with $R \le n$, it is at least $c\, n \log_2(n / \max(R,1))$;
3. for $R \le c_R n$ it is at least $c\, n (\log^* n + \max(0, \log_2(n/\max(R,1))))$.

Thus updates alone must pay these costs, regardless of how fast queries are.

## Proof sketch

The tree and the outer lemma are as in the query-inclusive bounds; only the inner game changes. There the receiver used query answers to recover the deleted keys; in the update-only game the key sequences are known to both players and the receiver instead recovers the stored values and the remaining keys from the memory states, which works because the uniformly random values carry enough entropy when $V \ge U^{2+\Omega(1)}/n^2$.

## Depends on

- [Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy](cell-probe-lower-bound-iterated-log-redundancy.md)

## Proof depends on

- [Inner communication game for succinct dictionaries](inner-communication-game.md)
- [Outer lemma: each tree node forces many attributed probes or many probes](outer-lemma.md)
- [Coin fixing for zero-error randomized cell-probe schemes](../cell-probe-complexity/coin-fixing-for-zero-error-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.

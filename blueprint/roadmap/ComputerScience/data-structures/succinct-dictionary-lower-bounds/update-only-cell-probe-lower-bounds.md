# Update-only cell-probe lower bounds for succinct dictionaries with large values

For every $\alpha_V > 0$ and $c_w \ge 0$ (and $c_R \ge 0$ for the iterated-log forms) there is a constant $c > 0$ such that for all $U, V, n$ with $2 \le n$, $3n \le U$, $V \ge 1$ and $U^{2 + \alpha_V} \le V n^2$, every deterministic step-indexed or zero-error randomized cell-probe scheme with words of $w \le c_w(\log_2 U + \log_2 V)$ bits implementing the dynamic dictionary exactly on admissible histories of length at most $3n+1$ satisfies, on the insert–delete distribution ($3n$ updates, no query time charged):

1. if $Sw \le \mathrm{OPT}(U,V,n) + c_R n \max(\log^{(k)} n, 1)$ with $1 \le k \le \log^* n$, the expected number of probes is at least $c\, n k$;
2. if $Sw \le \mathrm{OPT}(U,V,n) + R$ with $R \le n$, it is at least $c\, n \log_2(n / \max(R,1))$;
3. for $R \le c_R n$ it is at least $c\, n (\log^* n + \max(0, \log_2(n/\max(R,1))))$.

Thus updates alone must pay these costs, regardless of how fast queries are.

## Proof sketch

The argument of the query-inclusive bounds is repeated with a query-free inner game: the decoder recovers the deleted keys and the values of the segment from the memories alone, which is possible because the values carry enough entropy when $V$ is large compared with $U^2/n^2$.

## Depends on

- [Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy](cell-probe-lower-bound-iterated-log-redundancy.md)

## Proof depends on

- [Inner communication game for succinct dictionaries](inner-communication-game.md)
- [Outer lemma: each tree level forces linearly many probes](outer-lemma.md)
- [Coin fixing for zero-error randomized cell-probe schemes](../cell-probe-complexity/coin-fixing-for-zero-error-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), 2023; arXiv:2306.02253.

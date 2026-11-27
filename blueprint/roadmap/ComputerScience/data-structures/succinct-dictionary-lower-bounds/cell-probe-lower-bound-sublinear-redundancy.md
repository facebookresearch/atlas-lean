# Cell-probe lower bound Ω(log(n/R)) for dynamic dictionaries with sublinear redundancy

For every $\alpha > 0$, $\kappa \ge 1 + \alpha$ and $c_w \ge 0$ there are constants $c > 0$ and $n_0$ such that for all $U, V, n, R$ with $n \ge n_0$, $4n \le U$, $n^{1+\alpha} \le U$, $V \ge 1$, $UV \le n^{\kappa}$ and $0 \le R \le n$: every deterministic step-indexed or zero-error randomized cell-probe scheme with $S$ cells of $w \le c_w(\log_2 U + \log_2 V)$ bits that implements the dynamic dictionary with at most $n$ keys exactly on admissible histories of length at most $4n+1$, using $S w \le \log_2\binom{U}{n} + n \log_2 V + R$ bits, makes at least

$$
c \cdot n \cdot \log_2 \frac{n}{\max(R, 1)}
$$

expected probes on the insert–query–delete distribution. Combined with the iterated-log bound, for every $c_R \ge 0$ and all $R \le c_R n$ the expected probe count is at least $c \cdot n \left(\log^* n + \max\left(0, \log_2 \frac{n}{\max(R,1)}\right)\right)$.

## Proof sketch

Use a meta-operation tree whose level-1 blocks have $\max(R, n^{1-\gamma/2})$ meta-operations and whose fanout above level 1 is the constant $2^{64}$, so that it has $\Omega(\log(n/\max(R,1)))$ levels at which the outer lemma applies with $t = \Theta(\log U)$; aggregating the level bounds gives $\Omega(n \log(n/\max(R,1)))$ expected probes, and coin fixing handles zero-error randomized schemes. The combined bound takes the maximum of this and the iterated-log bound and uses $\max(a,b) \ge (a+b)/2$.

## Depends on

- [Cell-probe lower bound Ω(k) for dynamic dictionaries with n·log^(k) n redundancy](cell-probe-lower-bound-iterated-log-redundancy.md)

## Proof depends on

- [Outer lemma: each tree node forces many attributed probes or many probes](outer-lemma.md)
- [Aggregating level bounds over the meta-operation tree](aggregating-level-bounds.md)
- [Coin fixing for zero-error randomized cell-probe schemes](../cell-probe-complexity/coin-fixing-for-zero-error-cell-probe-schemes.md)

## Sources

- T. Li, J. Liang, H. Yu and R. Zhou, "Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries", Proceedings of the 64th IEEE Symposium on Foundations of Computer Science (FOCS), pp. 1842-1862, 2023; arXiv:2306.02253.

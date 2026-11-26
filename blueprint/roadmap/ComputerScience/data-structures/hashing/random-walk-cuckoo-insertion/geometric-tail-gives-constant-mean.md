# A geometric tail bound gives constant expected walk length

Let $T$ be the insertion time of a random walk. If there are constants $C \ge 1$ and $\rho \in (0, 1)$ such that $\Pr[T > \ell] \le C \rho^{\ell}$ for all $\ell \ge 0$, then $\mathbb{E}[T] \le C/(1 - \rho)$.

## Proof sketch

$\mathbb{E}[T] = \sum_{\ell \ge 0} \Pr[T > \ell] \le C \sum_{\ell \ge 0} \rho^{\ell} = C/(1-\rho)$.

## Depends on

- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
- Nikolaos Fountoulakis, Konstantinos Panagiotou, Angelika Steger, "On the Insertion Time of Cuckoo Hashing", SIAM Journal on Computing 42(6) (2013).

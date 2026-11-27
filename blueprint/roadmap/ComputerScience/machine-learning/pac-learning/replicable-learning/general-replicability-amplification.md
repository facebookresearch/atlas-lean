# Amplification of replicability from rho below one quarter

Let $\alpha > 0$ and let $A$ be $\rho$-replicable over a distribution $D$ with $\rho < 1/4 - \alpha$, using $m$ samples and erring with probability at most $\beta$. Then for every $\rho'$ with $0 < \rho' < \rho$ there is a $\rho'$-replicable algorithm $A'$ for $D$ with sample complexity $\tilde O\big(m \log^3(1/\beta)/(\rho'^2 \alpha^2)\big)$ that errs with probability at most $O(\beta + \rho')$ (Impagliazzo, Lei, Pitassi and Sorrell, Corollary A.4). The algorithm $A'$ draws $k = O(\log(1/\beta))$ shared random strings $r_1, \dots, r_k$ for $A$, runs the replicable heavy-hitters algorithm on the output distributions of $A$ with these strings (sampling each by running $A$ on fresh samples), and outputs the first heavy hitter returned, or $\bot$ if every call returns the empty list; its construction does not depend on $D$, so it serves every distribution of a family $\mathcal{D}$ over which $A$ satisfies the hypotheses (proof of Theorem A.3).

## Proof sketch

A $\rho$-replicable algorithm is $(\rho/x, x)$-replicable: for all but an $x$-fraction of random strings $r$, the output distribution $D_r$ of $A$ with string $r$ has an element of probability at least $1 - \rho/x$. Taking $x = 1/2 - \alpha$, Theorem A.3 applies for every $\rho < 1/4$. For a good string $r$ the replicable heavy-hitters algorithm, with thresholds set so that it returns the unique majority element of $D_r$, returns it with probability at least $1 - \rho'/k$, and for strings without a majority element it returns the empty list with probability at least $1 - \rho'/k$; two runs with the same shared randomness disagree only if some call disagrees, which costs at most $\rho'/k$ per call. All $k$ calls return the empty list with probability at most $(3/4)^k \le \beta$, and a returned majority element is incorrect with conditional probability $O(\beta + \rho')$ (proofs of Theorem A.3 and Corollary A.4).

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)
- [Randomized-threshold and random-grid rounding lemmas](randomized-rounding-disagreement.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022, Appendix A, Theorem A.3 and Corollary A.4; open copy: <https://arxiv.org/abs/2201.08430>.

# A geometric tail bound gives constant expected walk length

Let $T$ be a random variable taking values in $\{0, 1, 2, \dots\}$. If there are constants $C \ge 1$ and $\rho \in (0, 1)$ such that $\Pr[T > \ell] \le C \rho^{\ell}$ for all integers $\ell \ge 0$, then $\mathbb{E}[T] \le C/(1 - \rho)$. This applies in particular to the insertion time of random-walk insertion for $d$-ary cuckoo hashing (a positive integer) whenever its tail is geometric; for the uniform random walk such a geometric tail is conjectured by Bell and Frieze (Conjecture 9.2), not proved.

## Proof sketch

By the tail-sum formula for a random variable with values in $\{0, 1, 2, \dots\}$, $\mathbb{E}[T] = \sum_{i \ge 1} \Pr[T \ge i] = \sum_{\ell \ge 0} \Pr[T > \ell] \le C \sum_{\ell \ge 0} \rho^{\ell} = C/(1-\rho)$.

Bell and Frieze do not need a geometric tail for constant expected insertion time: they prove that the tail of the random walk decays faster than any polynomial and deduce $O(1)$ expected insertion time from that (their Corollary 9.1); any tail $O(\ell^{-1.01})$ would already suffice. They conjecture, but do not prove, the exponential tail $C_8 C_9^{-\ell}$ (Conjecture 9.2).

## Depends on

- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394, Section 9 (Corollary 9.1 and Conjecture 9.2).
- UC Berkeley CS 70, Course Notes, Note 19 ("Geometric and Poisson Distributions"), Theorem 19.1 (tail sum formula).
- Nikolaos Fountoulakis, Konstantinos Panagiotou, Angelika Steger, "On the Insertion Time of Cuckoo Hashing", SIAM Journal on Computing 42(6) (2013).

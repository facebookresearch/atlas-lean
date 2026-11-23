# Criterion for a uniform bound on the least non-Wieferich base

The following are
equivalent:
(a) there is a natural number $M$ such that for every odd prime $p$ there is an integer $N$ with
$1 \le N \le M$, $p \nmid N$ and $p^2 \nmid N^{p-1} - 1$;
(b) there is a natural number $M \ge 3$ such that only finitely many primes $p$ satisfy
$p^2 \mid N^{p-1} - 1$ for every integer $N$ with $2 \le N \le M$.

For $p \nmid N$ the condition $p^2 \nmid N^{p-1} - 1$ says that $p$ does not divide the Fermat
quotient $q_p(N) = (N^{p-1} - 1)/p$, so (a) bounds, uniformly in $p$, the least such base $N$;
(b) says that $\bigcap_{N=2}^{M} W(N)$ is finite, where $W(N)$ is the set of primes $p$ with
$N^{p-1} \equiv 1 \pmod{p^2}$.

## Sources

- Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of Level N*, INTEGERS 24 (2024), Article A22, Lemma 3.

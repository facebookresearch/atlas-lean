# AimPL one-bounded question on Elliott's conjecture along a subsequence

The statement that for every multiplicative $f : \mathbb{N} \to \mathbb{C}$ with $|f(n)| \le 1$ that is non-pretentious, there is a sequence of natural numbers $X_j \to \infty$ with $\frac{1}{X_j} \sum_{1 \le n \le X_j} f(n)\overline{f(n+1)} \to 0$; here non-pretentious means that for every modulus $q \ge 1$, every Dirichlet character $\chi$ modulo $q$ and every real $t$, the series $\sum_p \bigl(1 - \operatorname{Re}(f(p)\overline{\chi(p)} p^{it})\bigr)/p$ over the primes is not absolutely summable, which for $|f| \le 1$, where its terms are nonnegative, says that it diverges.

AimPL Problem 7.4 as printed takes $f : \mathbb{N} \to \mathbb{C}$ with no bound; this is its one-bounded first question, and the bound matters: for the positive completely multiplicative $f$ with $f(2) = 8$ and $f(p) = 1/p$ for odd primes $p$, the series diverges for every twist, but for $n = 2^k \le X < 2n$ the single term $f(n)f(n+1) = n^3/(n+1)$ makes the correlation average at least $n^2/(2(n+1))$, so no subsequence tends to $0$.

This page records the statement as a proposition. Its resolution: [Two-point Elliott conjecture along a subsequence of scales, for one-bounded functions](subsequence-two-point-holds.md).

## Sources

- AimPL: Sarnak's conjecture, Section 7, Problem 7.4, https://aimpl.org/sarnakconjecture/7/.

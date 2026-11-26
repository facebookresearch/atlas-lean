# Two-point Elliott conjecture along a subsequence of scales, for one-bounded functions

For every multiplicative $f : \mathbb{N} \to \mathbb{C}$ with $|f(n)| \le 1$ that is non-pretentious, there is a sequence of natural numbers $X_j \to \infty$ with $\frac{1}{X_j} \sum_{1 \le n \le X_j} f(n)\overline{f(n+1)} \to 0$; here non-pretentious means that for every modulus $q \ge 1$, every Dirichlet character $\chi$ modulo $q$ and every real $t$, the series $\sum_p \bigl(1 - \operatorname{Re}(f(p)\overline{\chi(p)} p^{it})\bigr)/p$ over the primes is not absolutely summable, which for $|f| \le 1$, where its terms are nonnegative, says that it diverges.

This resolves [AimPL one-bounded question on Elliott's conjecture along a subsequence](subsequence-two-point.md), the statement recorded as a proposition, in the affirmative; the resolution is due to Klurman, Mangerel and Teräväinen (2023), cited under Sources: their Theorem 1.2, applied to $f$ and its conjugate $\bar f$, gives the statement; pretentiousness is Definition 1.1 there. It answers the one-bounded first question of AimPL Problem 7.4; without the bound $|f(n)| \le 1$ the answer is negative.

## Sources

- AimPL: Sarnak's conjecture, Section 7, Problem 7.4, https://aimpl.org/sarnakconjecture/7/.
- O. Klurman, A. P. Mangerel and J. Teräväinen, On Elliott's conjecture and applications, arXiv:2304.05344v2 (2023), Theorem 1.2, https://arxiv.org/pdf/2304.05344v2; published in Proceedings of the London Mathematical Society 133 (2026), https://doi.org/10.1112/plms.70205.

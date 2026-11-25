# Pitman's representation theorem, existence half

Let $r_{b,k}$, for natural numbers $2 \le k \le b$, be real numbers that are nonnegative and consistent:

$$r_{b,k} = r_{b+1,k} + r_{b+1,k+1} \quad \text{for all } 2 \le k \le b.$$

Then there is a finite measure $\Lambda$ on $[0, 1]$ whose [merger rates](merger-rate.md) are these numbers: $r_{b,k} = \lambda_{b,k}$ for all $2 \le k \le b$. By [uniqueness in Pitman's representation](eq-of-merger-rate-eq.md), $\Lambda$ is unique. Consistency makes the sequence $m_i = r_{i+2,i+2}$ completely monotone, and Hausdorff's moment theorem gives a finite measure with moments $m_i$.

## Sources

- J. Pitman, *Coalescents with multiple collisions*, Ann. Probab. 27 (1999), 1870–1902, Theorem 1.
- F. Hausdorff, *Summationsmethoden und Momentfolgen. I*, Math. Z. 9 (1921), 74–109.

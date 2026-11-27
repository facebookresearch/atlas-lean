# Yao's theorem: the quadrangle inequality propagates to the optimal cost

If $w$ satisfies the quadrangle inequality and is monotone on intervals, then the optimal cost $c$ of the interval recurrence satisfies the quadrangle inequality. Knuth's weight $w$ (with nonnegative $p, q$) satisfies both hypotheses (with equality in the quadrangle inequality).

## Proof sketch

Induction on $j' - i$: write $c(i, j')$ and $c(i', j)$ with their optimal roots and recombine the four subintervals, using the quadrangle inequality for $w$ and the induction hypothesis on the smaller intervals.

## Depends on

- [The quadrangle inequality and monotonicity on intervals](quadrangle-inequality.md)

## Sources

- F. F. Yao, "Efficient Dynamic Programming Using Quadrangle Inequalities", Proceedings of the 12th ACM Symposium on Theory of Computing (STOC), 1980.

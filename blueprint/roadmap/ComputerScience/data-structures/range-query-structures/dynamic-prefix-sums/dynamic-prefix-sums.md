# Dynamic prefix sums problem

The *dynamic prefix sums* problem over an additive commutative monoid $(M, +, 0)$ maintains a list $A = (A_0, \dots, A_{n-1}) \in M^n$ under $\mathrm{add}(i, \delta)$, which replaces $A_i$ by $A_i + \delta$ (a no-op if $i \ge n$), and $\mathrm{sum}(\ell)$, which returns $A_0 + \dots + A_{\min(\ell, n) - 1}$. The length of the list never changes.

## Depends on

- [State-transition specification of a data structure](../../data-structure-interfaces-and-refinement/state-transition-specification.md)

## Sources

- P. M. Fenwick, "A New Data Structure for Cumulative Frequency Tables", Software: Practice and Experience 24(3), pp. 327-336, 1994.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
- M. L. Fredman and M. E. Saks, "The Cell Probe Complexity of Dynamic Data Structures", Proceedings of the 21st ACM Symposium on Theory of Computing (STOC), pp. 345-354, 1989.

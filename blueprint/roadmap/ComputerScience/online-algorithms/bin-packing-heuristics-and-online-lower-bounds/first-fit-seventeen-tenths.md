# First Fit uses at most 17/10 OPT + 4/5 bins

For every instance and every packing $Q$ of the same items, First Fit uses $FF$ bins with $10\,FF \le 17\,|Q| + 8$. Hence $FF \le \frac{17}{10}\mathrm{OPT} + \frac45$, and since $FF$ is an integer, $FF \le \lceil \frac{17}{10}\mathrm{OPT} \rceil$, sharpening the bound $\frac{17}{10}\mathrm{OPT} + 2$ of Johnson, Demers, Ullman, Garey and Graham.

## Proof sketch

By the theorem of Dósa and Sgall, $FF \le \lfloor 1.7\,\mathrm{OPT} \rfloor \le 1.7\,|Q|$.

## Depends on

- [Next Fit and First Fit](next-fit-and-first-fit.md)

## Sources

- G. Dósa and J. Sgall, "First Fit Bin Packing: A Tight Analysis", 30th International Symposium on Theoretical Aspects of Computer Science (STACS), 2013.
- M. R. Garey, R. L. Graham, D. S. Johnson and A. C.-C. Yao, "Resource Constrained Scheduling as Generalized Bin Packing", Journal of Combinatorial Theory, Series A 21(3), 1976.
- D. S. Johnson, A. Demers, J. D. Ullman, M. R. Garey and R. L. Graham, "Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms", SIAM Journal on Computing 3(4), 1974.

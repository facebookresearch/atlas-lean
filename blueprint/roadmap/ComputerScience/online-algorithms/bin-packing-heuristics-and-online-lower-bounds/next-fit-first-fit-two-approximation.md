# Next Fit and First Fit use fewer than 2 OPT bins

Every two consecutive bins produced by Next Fit, and every two bins produced by First Fit, are jointly overfull. A packing with $m \ge 2$ bins in which consecutive bins are jointly overfull holds total size more than $C \lfloor m/2 \rfloor$, so it uses fewer than $2\,\mathrm{OPT}$ bins; in particular, on every nonempty instance, Next Fit and First Fit use at most $2\,\mathrm{OPT} - 1$ bins.

## Proof sketch

Pair consecutive bins; each pair has total size above $C$. Hence $C\lfloor m/2 \rfloor < \sum a_i \le C \cdot \mathrm{OPT}$.

## Depends on

- [Next Fit and First Fit](next-fit-and-first-fit.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms/approximation-algorithms-and-approximation-ratios.md)

## Sources

- D. S. Johnson, "Near-Optimal Bin Packing Algorithms", PhD thesis, Massachusetts Institute of Technology, 1973.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.

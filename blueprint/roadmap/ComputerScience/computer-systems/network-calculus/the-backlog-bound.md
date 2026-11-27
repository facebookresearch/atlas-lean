# The backlog bound

Assume a flow constrained by a finite [arrival curve](arrival-curves.md) $\alpha$ ($\alpha(t) < \infty$ for every $t$) traverses a system that offers a [service curve](service-curves.md) $\beta$. Then for all $t$ the backlog satisfies

$$
R(t) - R^*(t) \le \sup_{s \ge 0} \{ \alpha(s) - \beta(s) \} = v(\alpha, \beta),
$$

the [vertical deviation](min-plus-algebra/vertical-and-horizontal-deviations.md) between the two curves.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Service curves](service-curves.md)
- [Vertical and horizontal deviations](min-plus-algebra/vertical-and-horizontal-deviations.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.1, Theorem 1.4.1 with its proof.

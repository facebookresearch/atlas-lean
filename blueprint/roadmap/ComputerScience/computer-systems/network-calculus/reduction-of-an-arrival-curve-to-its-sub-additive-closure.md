# Reduction of an arrival curve to its sub-additive closure

A flow is constrained by a wide-sense increasing function $\alpha$ if and only if it is constrained by its [sub-additive closure](min-plus-algebra/sub-additive-closure.md) $\bar\alpha$. So every [arrival curve](arrival-curves.md) may be replaced by a good one, which is never larger. For example, a flow of cells constrained by $3v_{10,0}$ (three periodic sources of period $10$) and arriving on a link of one cell per slot has arrival curve $\alpha_1 = \min(3v_{10,0}, v_{1,0})$, where $v_{T,0}(t) = \lceil t/T \rceil$ for $t > 0$; that curve allows $6$ cells in $11$ slots, while its closure allows only $\alpha_1(10) + \alpha_1(1) = 4$.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Sub-additive closure](min-plus-algebra/sub-additive-closure.md)

## Proof depends on

- [Arrival curves as min-plus inequalities](arrival-curves-as-min-plus-inequalities.md): $\alpha \otimes \alpha$, and by iteration every $\alpha^{(n)}$, is an arrival curve.
- [The sub-additive closure is the largest good minorant](min-plus-algebra/the-sub-additive-closure-is-the-largest-good-minorant.md): $\bar\alpha \le \alpha$.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.2.3, Theorem 1.2.1 with its proof and the example of Figure 1.6.

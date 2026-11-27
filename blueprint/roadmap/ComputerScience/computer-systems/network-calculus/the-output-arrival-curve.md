# The output arrival curve

Assume a flow constrained by a finite [arrival curve](arrival-curves.md) $\alpha$ ($\alpha(t) < \infty$ for every $t$, so that the deconvolution below is defined) traverses a system that offers a [service curve](service-curves.md) $\beta$. Then the output flow is constrained by the arrival curve $\alpha^* = \alpha \oslash \beta$, the [min-plus deconvolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md) of $\alpha$ by $\beta$.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Service curves](service-curves.md)
- [Min-plus convolution and deconvolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.1, Theorem 1.4.3 with its proof.

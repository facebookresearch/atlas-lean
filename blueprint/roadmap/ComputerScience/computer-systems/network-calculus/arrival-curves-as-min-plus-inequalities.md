# Arrival curves as min-plus inequalities

A flow $R$, with $R(t) = 0$ for $t < 0$, is constrained by an [arrival curve](arrival-curves.md) $\alpha$ if and only if $R \le R \otimes \alpha$, that is $R(t) \le \inf_{0 \le s \le t}\{R(s) + \alpha(t - s)\}$ for all $t \ge 0$. If $\alpha_1$ and $\alpha_2$ are arrival curves for $R$, then so is $\alpha_1 \otimes \alpha_2$.

## Depends on

- [Arrival curves](arrival-curves.md)
- [Min-plus convolution and deconvolution](min-plus-algebra/min-plus-convolution-and-deconvolution.md)

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.2.3, Lemmas 1.2.3 and 1.2.4 with their proofs.

# Concatenation of service curves

Assume a flow traverses systems $S_1$ and $S_2$ in sequence, and $S_i$ offers the [service curve](service-curves.md) $\beta_i$ to the flow, $i = 1, 2$. Then the concatenation of the two systems offers the service curve $\beta_1 \otimes \beta_2$ to the flow. Since min-plus convolution is commutative, the resulting bounds do not depend on the order of the systems.

**Proof.** With $R_1$ the output of $S_1$, $R_1 \ge R \otimes \beta_1$ and $R^* \ge R_1 \otimes \beta_2 \ge (R \otimes \beta_1) \otimes \beta_2 = R \otimes (\beta_1 \otimes \beta_2)$, using that convolution is isotone and associative.

## Depends on

- [Service curves](service-curves.md)

## Proof depends on

- [Algebraic properties of min-plus convolution](min-plus-algebra/algebraic-properties-of-min-plus-convolution.md): isotonicity, associativity and commutativity.

## Sources

- J.-Y. Le Boudec and P. Thiran, *Network Calculus: A Theory of Deterministic Queuing Systems for the Internet*, Lecture Notes in Computer Science 2050, Springer, 2001; online version of 2022, <https://leboudec.github.io/netcal/latex/netCalBook.pdf>, whose numbering is used here, Section 1.4.3, Theorem 1.4.6 with its proof, and the remark after the example "Pay bursts only once".

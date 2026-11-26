# Order-three Davenport–Schinzel sequences have length $\Theta(n\,\alpha(n))$

Let $\alpha$ be the [inverse Ackermann function](inverse-ackermann-function.md). There are constants $c_1, c_2 > 0$ such that the maximum length $\lambda_3(n)$ of an order-three Davenport–Schinzel sequence over $n$ symbols satisfies $c_1\, n\, \alpha(n) \le \lambda_3(n) \le c_2\, n\, \alpha(n)$ for all $n \ge 1$ (Hart and Sharir). A finer form is $\lambda_3(n) = 2n\alpha(n) \pm O(n\sqrt{\alpha(n)})$, and the lower bound is realized geometrically: some $n$ segments in the plane have a lower envelope with $n\alpha(n) - O(n)$ pieces.

## Depends on

- [Davenport–Schinzel sequence](davenport-schinzel-sequence.md)
- [Inverse Ackermann function](inverse-ackermann-function.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 12 (Davenport–Schinzel sequences), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%2012.pdf>: the paragraph "Bounds for higher-order Davenport-Schinzel sequences" before Section 12.1: the inverse Ackermann hierarchy $\alpha_k$ and the bound $\lambda_3(n) = \Theta(n\alpha(n))$, the finer bound $\lambda_3(n) = 2n\alpha(n) \pm O(n\sqrt{\alpha(n)})$, and the paragraph "Realizing DS sequences as lower envelopes" ($n$ segments whose lower envelope has length $n\alpha(n) - O(n)$)

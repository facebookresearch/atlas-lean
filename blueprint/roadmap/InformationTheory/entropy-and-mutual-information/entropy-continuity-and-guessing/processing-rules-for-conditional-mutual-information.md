# Processing rules for conditional mutual information

Let $(C, A, B, M, D)$ be random variables on finite sets defined on a common finite probability space, with conditional mutual information $I(\cdot\,;\cdot \mid \cdot)$ in bits.

1. (Chain rules) $I((D, A); B \mid C) = I(D; B\mid C) + I(A; B \mid C, D)$, and symmetrically in the second argument.
2. (Conditional data processing) If $S = f(A)$ and $R = g(B)$ hold almost surely for functions $f, g$, then $I(S; R \mid C) \le I(A; B \mid C)$.
3. (Messages) If $I(M; B \mid C, A) = 0$, then $I(A; B \mid C, M) \le I(A; B \mid C)$.
4. (Private coins) If $R_0$, $R_1$ and $(A, B)$ are mutually independent, then $I((A, R_0); (B, R_1)) = I(A; B)$.
5. (Uniform fibers) If for every supported $a$ the conditional law of $B$ given $A = a$ is uniform on a set of size $c$, then $I(A; B) = H(B) - \log_2 c$.

## Proof sketch

Item 1 is the chain rule for entropy applied to the four-term expression of conditional mutual information. Item 2 follows from item 1: $I(A;B\mid C) = I((S, A); B\mid C) \ge I(S; B\mid C)$, and similarly for $R$. Item 3 expands $I(A, M; B \mid C)$ in two orders by the chain rule. Item 4 is the chain rule plus independence, and item 5 computes $H(B\mid A) = \log_2 c$.

## Depends on

- [Conditional mutual information of a finite joint law](../conditional-mutual-information/finite-conditional-mutual-information.md)
- [Chain rule for mutual information](../conditional-mutual-information/finite-mutual-information-chain-rule.md)

## Proof depends on

- [Chain rule for mutual information](../conditional-mutual-information/finite-mutual-information-chain-rule.md)
- [Data-processing inequality](../../information-inequalities/data-processing-inequality/measure-mutual-information-comp-le.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
- J. Januzelli, M. Rosulek and L. Roy, "Lower Bounds for Garbled Circuits from Shannon-Type Information Inequalities", Advances in Cryptology (CRYPTO 2025), 2025.

# Concavity of conditional entropy and the mixture bound

Let $(P_i)_{i \in I}$ be joint laws of a pair $(Y, X)$ on finite sets $\beta \times \alpha$, and $\lambda$ a distribution on the finite set $I$. Write $H(X \mid Y)_P$ for conditional entropy in bits and $\bar P = \sum_i \lambda(i) P_i$. Then

$$
\sum_i \lambda(i)\, H(X\mid Y)_{P_i} \le H(X \mid Y)_{\bar P} \le \sum_i \lambda(i)\, H(X \mid Y)_{P_i} + H(\lambda).
$$

## Proof sketch

Let $Z \sim \lambda$ select the component. The left inequality is $H(X\mid Y, Z) \le H(X\mid Y)$ (conditioning reduces entropy). The right one is $H(X \mid Y) \le H(X, Z \mid Y) = H(Z\mid Y) + H(X\mid Y, Z) \le H(\lambda) + H(X \mid Y, Z)$ by the chain rule.

## Depends on

- [Conditional entropy of a finite joint law](../conditional-entropy-and-mutual-information/finite-conditional-entropy.md)

## Proof depends on

- [Chain rule for entropy](../conditional-entropy-and-mutual-information/shannon-entropy-eq-add-finite-conditiona.md)
- [Conditioning does not increase entropy](../conditional-entropy-and-mutual-information/finite-conditional-entropy-le.md)

## Sources

- A. Winter, "Tight Uniform Continuity Bounds for Quantum Entropies: Conditional Entropy, Relative Entropy Distance and Energy Constraints", Communications in Mathematical Physics 347, 2016.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.

# Error of the maximum a posteriori estimator from conditional entropy

Let $(Y, X)$ have a joint law on finite sets $\beta \times \alpha$ and let $g^*(y) \in \arg\max_{x} \Pr[X = x \mid Y = y]$ be a maximum a posteriori estimator (arbitrary for $\Pr[Y=y] = 0$). Then $g^*$ minimizes $\Pr[g(Y) \ne X]$ over all deterministic estimators $g : \beta \to \alpha$, and, with $H(X\mid Y)$ in bits,

$$
\Pr[g^*(Y) \ne X] \le 1 - 2^{-H(X\mid Y)} \le (\ln 2)\, H(X\mid Y).
$$

This is a converse to Fano's inequality.

## Proof sketch

For each $y$ the most likely value has conditional probability $2^{-H_\infty(X\mid Y=y)} \ge 2^{-H(X\mid Y = y)}$, since min-entropy is at most Shannon entropy. Averaging over $y$ and applying Jensen's inequality to the convex function $t \mapsto 2^{-t}$ gives success probability at least $2^{-H(X\mid Y)}$; finally $1 - 2^{-t} \le t\ln 2$.

## Depends on

- [Conditional entropy of a finite joint law](../conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Maximum a posteriori hypothesis](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/is-map.md)

## Proof depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Sources

- J. Januzelli, M. Rosulek and L. Roy, "Lower Bounds for Garbled Circuits from Shannon-Type Information Inequalities", Advances in Cryptology (CRYPTO 2025), 2025.
- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.

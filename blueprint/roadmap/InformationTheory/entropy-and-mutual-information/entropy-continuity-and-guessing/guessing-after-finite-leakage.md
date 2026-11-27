# Guessing a secret after finite leakage

Let $p$ be a discrete distribution on a set $X$ (possibly infinite) with $p(x) \le m$ for every $x$, let $\mathrm{hint} : X \to Y$ take values in a finite set $T \subseteq Y$, and let $G : Y \to \Delta(X)$ be any randomized guessing strategy. Then

$$
\Pr_{x \sim p,\ x' \sim G(\mathrm{hint}(x))}[x' = x] = \sum_{x} p(x)\, G(\mathrm{hint}(x))(x) \le |T| \cdot m.
$$

In particular, a uniform $n$-bit string cannot be guessed from a $d$-bit hint with probability more than $2^{d - n}$, and a coordinate of independent uniform inputs on a finite set $X$ cannot be predicted from coordinatewise observations in a finite set $Y$ with probability more than $|Y|/|X|$.

## Proof sketch

Group the sum by the value $y \in T$ of the hint: for fixed $y$, $\sum_{x : \mathrm{hint}(x) = y} p(x) G(y)(x) \le m \sum_x G(y)(x) \le m$. Summing over the $|T|$ hint values gives the bound.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)

## Sources

- J. Januzelli, M. Rosulek and L. Roy, "Lower Bounds for Garbled Circuits from Shannon-Type Information Inequalities", Advances in Cryptology (CRYPTO 2025), 2025.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.

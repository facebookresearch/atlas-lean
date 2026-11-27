# Soundness of the Babai-Fortnow-Lund multilinearity test

Let $\mathbb{F}$ be a finite field, $n \ge 1$, $f : \mathbb{F}^n \to \mathbb{F}$, and suppose $|\mathbb{F}| \ge 40 n^2$, $0 \le \delta \le 1/(400 n^2)$ and $\varepsilon \le 1/(800 n^3)$. If for every direction $i$ fewer than $\varepsilon |\mathbb{F}|^n$ points $x$ lie on an axis-parallel line in direction $i$ that is not $\delta$-approximately affine for $f$, then there is a multilinear $g$ with

$$|\{x : f(x) \ne g(x)\}| < 3 n^2\Bigl(\varepsilon + \delta + \frac{1}{|\mathbb{F}|}\Bigr)|\mathbb{F}|^n.$$

At $\delta = 0$ this says that functions passing the line test with high probability are close to multilinear.

## Proof sketch

Correct $f$ one direction at a time: replace each axis-parallel line in direction $i$ by its nearest affine function, and show by counting bad lines that each round moves only an $O(n(\varepsilon + \delta + 1/|\mathbb{F}|))$ fraction of points while preserving approximate affineness in the directions already treated. After $n$ rounds the function is affine on every axis-parallel line, hence multilinear, and the accumulated changes give the stated bound.

## Depends on

- [Multilinear functions on F^n and the multilinearity test](multilinear-functions-and-the-multilinearity-test.md)

## Sources

- L. Babai, L. Fortnow, C. Lund, "Non-Deterministic Exponential Time Has Two-Prover Interactive Protocols", Computational Complexity, 1991.

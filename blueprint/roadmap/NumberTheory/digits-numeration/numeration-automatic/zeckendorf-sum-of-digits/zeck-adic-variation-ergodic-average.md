# Ergodic theorem for the Zeckendorf digit-sum variation

Let $\mu$ be a probability
measure on the digit sequences $x : \mathbb{N} \to \{0, 1\}$ that gives the complement of the
Zeckendorf-adic integers $\mathbb{X}$ measure zero and is preserved by the odometer $T$. Let
$r \ge 1$ and let $f : \mathbb{Z} \to \mathbb{C}$ be such that $f \circ \Delta^{(r)}$ is
$\mu$-integrable, where $\Delta^{(r)}$ is the variation on $\mathbb{X}$. Write $s(n)$ for the
number of terms in the Zeckendorf representation of $n$. Then

$$\frac{1}{N} \sum_{n=0}^{N-1} f\bigl(s(n + r) - s(n)\bigr) \to \int f(\Delta^{(r)}(x))\, d\mu(x)$$

as $N \to \infty$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Proposition 28 (`jis-2024-24.3.2-prop-28`).

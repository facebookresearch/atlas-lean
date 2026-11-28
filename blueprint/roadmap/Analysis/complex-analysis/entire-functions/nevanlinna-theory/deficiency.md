# Nevanlinna deficiency

For $f : \mathbb{C} \to \mathbb{C}$ and a value $a \in \mathbb{C} \cup \{\infty\}$, the deficiency is

$$
\delta(a, f) = \liminf_{r \to \infty} \frac{m(r, a)}{T(r, f)},
$$

where $m(r, a)$ is the proximity function and $T(r, f)$ the [Nevanlinna characteristic](nevanlinna-t.md). The quotient is computed in $\mathbb{R}$ with $x / 0 = 0$, and the liminf is the real liminf, which has no meaning of its own when the quotient is not eventually bounded.

For a nonconstant meromorphic $f$ these conventions do not matter: $T(r, f) \to \infty$ and, by the first main theorem, $0 \le m(r, a) \le T(r, f) + O(1)$, so the quotient is eventually defined and bounded and $\delta(a, f) = 1 - \limsup_{r\to\infty} N(r, a)/T(r, f)$ is the classical deficiency, with $0 \le \delta(a, f) \le 1$. For other inputs, such as a constant function (for instance $f = 0$), the value is fixed by the conventions and has no classical meaning.

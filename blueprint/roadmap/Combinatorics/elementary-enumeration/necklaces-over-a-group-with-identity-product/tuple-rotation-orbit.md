# Rotation orbit of a tuple

Let $x = (x_0, \dots, x_{n-1})$ be a tuple of length $n$ with
entries in a type $\alpha$, and let $\sigma$ be the cyclic rotation of $\{0, \dots, n-1\}$ that
sends $i$ to $i + 1$ for $i < n - 1$ and sends $n - 1$ to $0$. The rotation orbit of $x$ is the
set of tuples $x \circ \sigma^m$ for $m \in \mathbb{N}$, that is, of the cyclic shifts
$(x_m, x_{m+1}, \dots, x_{m+n-1})$ of $x$, with indices taken modulo $n$.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Definition 2.3 (the action of `C_n` by rotation; necklaces are its orbits), used by Theorem 16 (`jis-2026-26.4.6-thm-16`).

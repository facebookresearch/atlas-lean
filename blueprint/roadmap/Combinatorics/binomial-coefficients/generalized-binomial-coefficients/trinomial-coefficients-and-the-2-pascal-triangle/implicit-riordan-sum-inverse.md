# Inversion of an implicit Riordan array sum

Write $[t^m]F$ for the coefficient of $t^m$
in a power series $F$ and $F'$ for its formal derivative. Let $K$ be a field and let $f$,
$\psi$, $g$, $b$ be power series over $K$ with $f(0) \ne 0$, $\psi(0) \ne 0$ and $g(0) \ne 0$.
Put $h(t) = t\,g(t)$ and, for $m \in \mathbb{N}$, $a_m = [t^m]\,f(t)\,\psi(t)^m\,b(h(t))$. Then
for every $n \in \mathbb{N}$,

$$[t^n]\,b = \sum_{k=0}^{n} \left([t^{n-k}]\,
\frac{(\psi - t\psi')\,h'}{f\,\psi^{k+1}\,g^{n+1}}\right) a_k.$$

The paper writes the factor $1/g^{n+1}$ as $t^{n+1}/h(t)^{n+1}$ and does not state the
hypothesis $f(0) \ne 0$, which $1/f$ needs.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 47 (`jis-2025-25.3.5-thm-47`).

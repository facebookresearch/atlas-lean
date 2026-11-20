# Counting aperiodic necklaces with product in a conjugation-closed set

Let $G$ be a
finite group, let $K \subseteq G$ satisfy $g c g^{-1} \in K$ for all $g \in G$ and $c \in K$, and
let $n \ge 1$. For an $n$-tuple $x = (x_0, \dots, x_{n-1}) \in G^n$ let its rotation orbit be the
set of its cyclic rotations $(x_m, x_{m+1}, \dots, x_{m+n-1})$, $m \ge 0$, with indices taken mod
$n$. Then the number of rotation orbits with exactly $n$ elements of tuples $x$ with
$x_0 x_1 \cdots x_{n-1} \in K$ is

$$\frac{1}{n} \sum_{d \mid n} \mu(n/d) \, \#\{a \in G : a^{n/d} \in K\} \, |G|^{d-1},$$

where $\mu$ is the Möbius function.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 24 (`jis-2026-26.4.6-thm-24`).

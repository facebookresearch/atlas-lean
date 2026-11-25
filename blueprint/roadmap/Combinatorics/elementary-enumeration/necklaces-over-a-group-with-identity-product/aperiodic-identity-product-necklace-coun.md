# Counting aperiodic necklaces with identity product

Let $G$ be a finite group and
$n \ge 1$. For an $n$-tuple $x = (x_0, \dots, x_{n-1}) \in G^n$ let its rotation orbit be the set
of its cyclic rotations $(x_m, x_{m+1}, \dots, x_{m+n-1})$, $m \ge 0$, with indices taken mod
$n$. Then the number of rotation orbits with exactly $n$ elements of tuples $x$ with
$x_0 x_1 \cdots x_{n-1} = 1$ is

$$\frac{1}{n} \sum_{d \mid n} \mu(n/d) \, r_{n/d}(G) \, |G|^{d-1},$$

where $\mu$ is the Möbius function and $r_k(G)$ is the number of $g \in G$ with $g^k = 1$.

## Sources

- Darij Grinberg and Peter Mao, *Necklaces over a Group with Identity Product*, Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 16 (`jis-2026-26.4.6-thm-16`).

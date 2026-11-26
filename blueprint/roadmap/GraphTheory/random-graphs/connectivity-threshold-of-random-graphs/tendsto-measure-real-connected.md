# Connectivity threshold of $G(n, p)$ (Erdős–Rényi)

Let $c \in \mathbb{R}$ and let $p_n \in [0, 1]$ satisfy $p_n = (\log n + c)/n$ for all large $n$. Then

$$\Pr[G(n, p_n) \text{ is connected}] \to e^{-e^{-c}}.$$

Frieze and Karoński (Theorem 4.1) state the theorem for the uniform model $G(n, m)$ with $m = \tfrac12 n(\log n + c_n)$, which also covers $c_n \to \pm\infty$. Their proof first establishes this $G(n, p)$ form and then transfers it. Connectivity fails exactly when there is a component of order $k \le n/2$. The proof shows that, with high probability, the only such components are isolated vertices ($k = 1$), and then takes the Poisson limit of the number of isolated vertices from Theorem 3.1.

## Informally uses

- [No isolated vertex at the connectivity threshold (Erdős–Rényi)](tendsto-measure-real-no-isolated.md): the case $k = 1$, which gives the limit.

## Sources

- P. Erdős and A. Rényi, "On random graphs I", *Publ. Math. Debrecen* 6 (1959), 290–297 (not consulted directly).
- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Theorem 4.1 and its proof, which uses Theorem 3.1.

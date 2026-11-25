# Adding a small $r$ leaves the high digits unchanged

Write $F_j$ for the Fibonacci
numbers ($F_1 = F_2 = 1$). Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of
Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive ones), and write
$x + r = T^r(x)$ for the $r$-th iterate of the Zeckendorf odometer $T$. Let $x \in \mathbb{X}$,
$\ell \ge 2$ and $r < F_{\ell+1}$, and suppose that $x_{\ell+2} = x_{\ell+3} = 0$. Then
$(x + r)_k = x_k$ for every $k \ge \ell + 3$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Lemma 10 (`jis-2024-24.3.2-lem-10`).

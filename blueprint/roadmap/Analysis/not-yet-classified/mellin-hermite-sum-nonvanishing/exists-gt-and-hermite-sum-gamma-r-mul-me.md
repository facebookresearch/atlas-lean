# Gamma–Mellin Hermite sums are nonzero at arbitrarily large shifts

Let $m \in \mathbb{N}$,
$a \in \mathbb{Q}$ with $a \neq 0$, $u_3 \in \mathbb{C}$, $a_3 \in \mathbb{Z}/2$ and
$e \in \mathbb{Z}$, and suppose the admissible index set `hermiteAdmissible m a₃ e` is nonempty.
Let $H : \mathbb{N} \to \mathbb{Z}/2 \to \mathbb{R} \to \mathbb{C}$ be a family whose Mellin
transforms $M_{j,b} = \mathcal{M}(H_{j,b})$ satisfy two conditions, each for every
$\varepsilon > 0$ and all large real $x$:

* (`hA`) for every $j$ and every parity $b$, $M_{j,b}(x) \neq 0$ and

$$\Bigl\lVert M_{j,b}(x + 2) - \frac{x}{2\pi a^2} \, M_{j,b}(x) \Bigr\rVert
    \le \varepsilon \, x \, \lVert M_{j,b}(x) \rVert;$$

* (`hB`) for every $j$ and all parities $b$ and $b'$,

$$\lVert M_{j+1,b'}(x - 1) \rVert \le \varepsilon \, \lVert M_{j,b}(x) \rVert.$$

Then for every $\sigma_0 \in \mathbb{R}$ there is a real $s > \sigma_0$ with
`hermiteGammaMellinSum m a u₃ a₃ e H s ≠ 0`.

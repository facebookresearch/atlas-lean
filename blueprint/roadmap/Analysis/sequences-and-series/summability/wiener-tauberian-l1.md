# Wiener's Tauberian theorem on $L^1(\mathbb{R})$

Let $f : \mathbb{R} \to \mathbb{C}$ be
Lebesgue integrable, and suppose that its Fourier transform
$\hat f(w) = \int_{\mathbb{R}} e^{-2\pi i x w} f(x)\,dx$ vanishes at no real $w$. Then for every
Lebesgue integrable $g : \mathbb{R} \to \mathbb{C}$ and every $\varepsilon > 0$ there are a finite
set $S \subset \mathbb{R}$ and coefficients $c_t \in \mathbb{C}$ for $t \in S$ such that the
function $h(x) = g(x) - \sum_{t \in S} c_t f(x - t)$ is integrable and
$\int_{\mathbb{R}} |h(x)|\,dx < \varepsilon$. In other words, the translates of $f$ span a dense
subspace of $L^1(\mathbb{R})$.

## Sources

- N. Wiener, Ann. of Math. 33 (1932) 1–100, DOI 10.2307/1968102, Thm I; Rudin, Fourier Analysis on Groups

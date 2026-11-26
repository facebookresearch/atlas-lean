# Diagonal AdaGrad on a box: per-coordinate adaptive regret

Let $B = \prod_{i \in I}[l_i, r_i] \subseteq \mathbb{R}^I$ be a box with $r_i - l_i \le D$ for all $i$, $D > 0$, $\varepsilon \ge 0$, and let subgradients $g_t$ satisfy $f_t(x) + \sum_i g_t(x)_i(y_i - x_i) \le f_t(y)$ on $B$. Diagonal AdaGrad updates each coordinate separately, $x_{t+1,i} = \mathrm{clamp}_{[l_i, r_i]}\big(x_{t,i} - \gamma\, g_t(x_t)_i/\sqrt{\varepsilon + \sum_{s \le t} g_s(x_s)_i^2}\big)$. With $\gamma = D/\sqrt2$, for every $u \in B$,

$$
\sum_{t<T}(f_t(x_t) - f_t(u)) \le \sqrt2\, D\sum_{i \in I}\sqrt{\varepsilon + \sum_{t<T} g_t(x_t)_i^2} - \frac{D}{\sqrt2}\,|I|\sqrt{\varepsilon}.
$$

For $\varepsilon = 0$ this is at most the dense bound $\sqrt2\, D\sqrt{|I|\sum_i\sum_t g_{t,i}^2}$ by Cauchy-Schwarz, and improves on it when gradients are sparse.

## Proof sketch

Clamping to an interval is a Pythagorean projection in one dimension, and the diagonal update separates across coordinates, so the linearized regret splits into $|I|$ scalar AdaGrad problems on intervals of length at most $D$. Apply the scalar argument with the telescoping lemma in each coordinate and sum.

## Depends on

- [Online convex optimization protocol and projected online gradient descent](online-convex-optimization-and-projected-ogd.md)

## Proof depends on

- [Telescoping lemma $\sum a_t/\sqrt{\varepsilon + \sum_{s \le t} a_s} \le 2(\sqrt{\varepsilon + \sum a_t} - \sqrt{\varepsilon})$](adaptive-square-root-telescoping-lemma.md)

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

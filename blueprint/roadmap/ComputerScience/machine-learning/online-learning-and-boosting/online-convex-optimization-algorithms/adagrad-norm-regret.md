# AdaGrad-Norm: data-dependent regret $\sqrt2\, D \sqrt{\varepsilon + \sum \|g_t\|^2}$ without knowing G or T

AdaGrad-Norm is projected online gradient descent with the adaptive step $\eta_t = \gamma/\sqrt{S_t}$, where $S_t = \varepsilon + \sum_{s \le t}\|g_s(x_s)\|^2$ accumulates the observed squared subgradient norms ($\varepsilon \ge 0$, $\gamma > 0$). Let $K$ have diameter at most $D > 0$ and $x_0 \in K$. With $\gamma = D/\sqrt2$, for every $u \in K$ and $T$,

$$
\sum_{t<T}(f_t(x_t) - f_t(u)) \le \sqrt2\, D\sqrt{\varepsilon + \sum_{t<T}\|g_t(x_t)\|^2} - \frac{D}{\sqrt2}\sqrt{\varepsilon}.
$$

In particular, if $\|g_t\| \le G$ on $K$ and $\varepsilon = 0$, the regret is at most $\sqrt2\, GD\sqrt{T}$, without prior knowledge of $G$ or $T$.

## Proof sketch

The OGD analysis with nonincreasing steps bounds the regret by $D^2/(2\eta_{T-1}) + \sum_t \eta_t\|g_t\|^2/2 = \frac{D^2}{2\gamma}\sqrt{S_{T-1}} + \frac\gamma2\sum_t \|g_t\|^2/\sqrt{S_t}$. The telescoping lemma bounds the second sum by $2(\sqrt{S_{T-1}} - \sqrt\varepsilon)$, and $\gamma = D/\sqrt2$ minimizes $D^2/(2\gamma) + \gamma$.

## Depends on

- [Online convex optimization protocol and projected online gradient descent](online-convex-optimization-and-projected-ogd.md)

## Proof depends on

- [Telescoping lemma $\sum a_t/\sqrt{\varepsilon + \sum_{s \le t} a_s} \le 2(\sqrt{\varepsilon + \sum a_t} - \sqrt{\varepsilon})$](adaptive-square-root-telescoping-lemma.md)
- [Zinkevich's regret bound for projected online gradient descent](zinkevich-ogd-regret-bound.md)

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

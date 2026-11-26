# Telescoping lemma $\sum a_t/\sqrt{\varepsilon + \sum_{s \le t} a_s} \le 2(\sqrt{\varepsilon + \sum a_t} - \sqrt{\varepsilon})$

For every sequence $a_0, a_1, \ldots \ge 0$, every $\varepsilon \ge 0$ and every $T$,

$$
\sum_{t<T} \frac{a_t}{\sqrt{\varepsilon + \sum_{s \le t} a_s}} \le 2\left(\sqrt{\varepsilon + \sum_{t<T} a_t} - \sqrt{\varepsilon}\right),
$$

with the convention $0/0 = 0$ for terms whose denominator vanishes.

## Proof sketch

With $S_t = \varepsilon + \sum_{s \le t} a_s$, each term satisfies $a_t/\sqrt{S_t} = (S_t - S_{t-1})/\sqrt{S_t} \le 2(\sqrt{S_t} - \sqrt{S_{t-1}})$, since $x - y \le 2\sqrt{x}(\sqrt{x} - \sqrt{y})$ for $x \ge y \ge 0$. Summing telescopes.

## Sources

- Francesco Orabona, "A Modern Introduction to Online Learning", lecture notes, 2019.
- Elad Hazan, "Introduction to Online Convex Optimization", MIT Press, 2022.

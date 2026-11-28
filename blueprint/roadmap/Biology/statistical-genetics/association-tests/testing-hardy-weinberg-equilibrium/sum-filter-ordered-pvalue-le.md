# Ordered p-values are super-uniform, combinatorial form

Let $f : \mathbb{N} \to \mathbb{R}$ be nonnegative, $g : \mathbb{N} \to \mathbb{R}$ any key,
$M \in \mathbb{N}$ and $t \ge 0$. Then the $f$-mass of the outcomes $h < M$ whose
[ordered p-value](ordered-pvalue.md) is at most $t$ is at most $t$:

$$\sum_{h < M,\ \mathrm{pv}_{f, g, M}(h) \le t} f(h) \le t.$$

If $h_0$ is the least extreme of these outcomes (largest $g$), all of them are at least as extreme
as $h_0$, so their mass is at most $\mathrm{pv}_{f, g, M}(h_0) \le t$ (Lehmann and Romano 2005,
Lemma 3.3.1).

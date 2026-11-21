# Bilinear forms are bounded by the cut norm

Let $V$ be a finite set and $u$ a real function on the unordered pairs $\{x, y\}$ of elements of $V$ (loops $\{x, x\}$ included), written $u(x, y) = u(y, x)$. For all $a, b : V \to [0, 1]$,

$$\Big\lvert \sum_{x, y \in V} a(x)\, b(y)\, u(x, y) \Big\rvert \le \max_{S, T \subseteq V} \Big\lvert \sum_{x \in S} \sum_{y \in T} u(x, y) \Big\rvert,$$

the right side being the [unnormalized cut norm](cut-max.md) of $u$ (Borgs–Chayes–Lovász–Sós–Vesztergombi, *Convergent sequences of dense graphs I*, Adv. Math. 219 (2008), equation (3.3), finite form).

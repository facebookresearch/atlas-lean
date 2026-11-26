# Tightness in `C([0,1])` from tight initial values and a modulus of continuity

(Billingsley 1999, Theorem 7.3, sufficiency.) Let $(\Omega, P)$ be a probability space and, for each $n \in \mathbb{N}$, let $W_n : \Omega \to C([0,1], \mathbb{R})$ be measurable. Assume:

1. the laws of the starting values $W_n(\cdot)(0)$, $n \in \mathbb{N}$, form a tight family of measures on $\mathbb{R}$;
2. for every $\varepsilon > 0$ and $b > 0$ there is $\delta > 0$ such that for all sufficiently large $n$,

$$P\bigl(\{\omega : \exists\, s, t \in [0,1],\ |s - t| \le \delta,\ |W_n(\omega)(s) - W_n(\omega)(t)| \ge \varepsilon\}\bigr) \le b.$$

Then the laws of the paths $W_n$, $n \in \mathbb{N}$, form a tight family of measures on $C([0,1], \mathbb{R})$.

The proof recentres each path at its starting value, $V_n(\omega) = W_n(\omega) - W_n(\omega)(0)$. The recentred paths vanish at $0$ and have the same oscillation events, so the pinned criterion gives a compact set capturing $V_n$; tightness of the initial laws gives a compact set of starting values; adding the constant starting path back is continuous, so the image of the product of the two compact sets is compact and captures $W_n$ up to the sum of the two exceptional probabilities.

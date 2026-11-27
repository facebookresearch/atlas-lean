# Optimal online contention resolution for matroids

Every matroid admits a $\frac12$-selectable OCRS when the arrival order is fixed in advance and known to the scheme, and $\frac12$ is optimal; moreover every matroid admits a $(1 - 1/e)$-selectable random-order contention resolution scheme, where elements arrive in uniformly random order, and $1 - 1/e$ is optimal. Both optimality claims hold already for rank-one matroids.

## Proof sketch

Lee and Singla write the existence of a $c$-selectable scheme as an exponential-size linear program whose variables are deterministic schemes, and show that its dual is an *ex-ante prophet inequality*: a prophet inequality measured against the ex-ante relaxation $\max_{x \in P_{\mathcal{M}}} \sum_e x_e\,\mathbb{E}[X_e \mid X_e \text{ in its top } x_e \text{ quantile}]$, which upper-bounds the prophet's expected optimum. They then prove a $\frac12$ ex-ante prophet inequality for adversarial order by adapting the balanced thresholds of Kleinberg and Weinberg, and a $(1 - 1/e)$ ex-ante prophet inequality for random order with uniform arrival times in $[0, 1]$ and thresholds scaled by $1 - e^{t-1}$ at time $t$. Optimality: for adversarial order take two elements with $x_1 = 1 - \epsilon$ and $x_2 = \epsilon$; for random order take $x_e = 1/n$ for $n$ elements, where with probability $(1 - 1/n)^n$ no element is active.

## Depends on

- [Online contention resolution schemes](online-contention-resolution.md)

## Proof depends on

- [Kleinberg–Weinberg: every matroid admits a $1/2$ prophet inequality](matroid-prophet-half.md)
- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Euiwoong Lee, Sahil Singla, "Optimal Online Contention Resolution Schemes via Ex-Ante Prophet Inequalities", ESA (2018), arXiv:1806.09251, Theorems 1.4, 1.5, 3.8 and Corollary 1.6.

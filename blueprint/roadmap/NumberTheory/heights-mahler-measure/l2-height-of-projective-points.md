# ℓ²-height of a point of projective space

Let $N \ge 0$ and let $P \in \mathbb{P}^N(\overline{\mathbb{Q}})$. Choose a number field $K$ and
homogeneous coordinates $x = (x_0, \dots, x_N) \in K^{N+1} \setminus \{0\}$ of $P$. The
**$\ell^2$-logarithmic Weil height** of $P$ is

$$h_2(P) = \frac{1}{[K : \mathbb{Q}]} \Biggl( \sum_{\mathfrak{p}} \log \max_{0 \le i \le N}
  \|x_i\|_{\mathfrak{p}} + \sum_{\sigma : K \to \mathbb{C}} \log \Bigl( \sum_{i=0}^{N}
  |\sigma(x_i)|^2 \Bigr)^{1/2} \Biggr),$$

where $\mathfrak{p}$ runs over the nonzero prime ideals of $\mathcal{O}_K$, with
$\|y\|_{\mathfrak{p}} = N(\mathfrak{p})^{-v_{\mathfrak{p}}(y)}$ for $y \ne 0$ and
$\|0\|_{\mathfrak{p}} = 0$, and $\sigma$ runs over all $[K : \mathbb{Q}]$ field embeddings of $K$
into $\mathbb{C}$, so that a pair of complex conjugate embeddings contributes twice. By the product
formula $\sum_{\mathfrak{p}} \log \|a\|_{\mathfrak{p}} + \sum_{\sigma} \log |\sigma(a)| = 0$
for $a \in K^\times$, the height $h_2(P)$ does not depend on the choice of coordinates, and it does not
depend on $K$. Equivalently, $[K : \mathbb{Q}] \, h_2(P)$ is the arithmetic degree
$\widehat{\deg}(\varepsilon_P^* \overline{\mathcal{O}(1)})$ for the morphism $\varepsilon_P \colon
\operatorname{Spec} \mathcal{O}_K \to \mathbb{P}^N_{\mathbb{Z}}$ extending $P$, with
$\mathcal{O}(1)$ given the Fubini–Study metric $\|X_j\|(x) = |x_j| / (\sum_i |x_i|^2)^{1/2}$ at
each embedding; when $K$ is the residue field of $P$, this is the height of the Zariski closure of
$P$ in $\mathbb{P}^N_{\mathbb{Z}}$ for this metric, not divided by $[K : \mathbb{Q}]$.

With the maximum $\max_i |\sigma(x_i)|$ in place of the $\ell^2$ norm at the embeddings one gets
the usual absolute logarithmic Weil height $h(P)$, and $h(P) \le h_2(P) \le h(P) + \frac{1}{2}
\log (N + 1)$, since $\max_i |y_i| \le (\sum_i |y_i|^2)^{1/2} \le \sqrt{N + 1} \, \max_i |y_i|$. In
particular $h_2(P) \ge 0$.

## Depends on

- [Height of a cycle](../../AlgebraicGeometry/arakelov-geometry/height-of-a-cycle.md), for the
  arithmetic degree of a point of $\mathbb{P}^N_{\mathbb{Z}}$ with the Fubini–Study metric

## Proof depends on

- [Principal Arakelov divisors have size one](../../AlgebraicGeometry/arakelov-geometry/arakelov-divisors/size-principal.md),
  for the product formula, which makes $h_2(P)$ independent of the coordinates

## Sources

- F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
  <https://doi.org/10.24033/bsmf.2623>, §2.3.4, p. 30: the $\ell^2$-logarithmic Weil height of a
  point of $\mathbb{P}^N(\overline{\mathbb{Q}})$, defined with the hermitian $\ell^2$ norms at the
  infinite places, as the height with respect to $\mathcal{O}(1)$ with the Fubini–Study metric;
  arXiv:0907.1458.

# Height of a cycle

Let $X$ be a proper flat scheme over $\mathbb{Z}$ and $\bar L$ a hermitian line bundle on $X$. For
an integer $p \ge 0$ and a cycle $Z \in Z_p(X)$ of dimension $p$, the dimension being that of a
subscheme of $X$, the height of $Z$ with respect to $\bar L$ is the real number
$$h_{\bar L}(Z) = \widehat{\deg}\bigl( \hat c_1(\bar L)^p \mid Z \bigr),$$
the arithmetic degree of $Z$ with respect to $p$ copies of $\bar L$. A cycle flat over $\mathbb{Z}$
has generic fibre of dimension $p - 1$. For a closed point $z$, $h_{\bar L}(z) = \log \# \kappa(z)$.
If $Z$ is integral and lies over a prime $\ell$, then $h_{\bar L}(Z) = \deg\bigl(
c_1(L|_{X_{\mathbb{F}_\ell}})^p \mid Z \bigr) \log \ell$. If $Z$ is the Zariski closure of a closed
point $z$ of $X_\mathbb{Q}$, with residue field $K = \kappa(z)$, then $Z$ is the image of the
morphism $\varepsilon_z \colon \operatorname{Spec} \mathcal{O}_K \to X$ extending $z$ and
$h_{\bar L}(Z) = \widehat{\deg}(\varepsilon_z^* \bar L)$ is the arithmetic degree of a hermitian
line bundle on $\operatorname{Spec} \mathcal{O}_K$.

Chambert-Loir normalizes the height by the degree. Write $X = \mathcal{X}_\mathbb{Q}$ and
$L = \mathcal{L}_\mathbb{Q}$ for a proper flat scheme $\mathcal{X}$ over $\mathbb{Z}$ with a
hermitian line bundle $\bar{\mathcal{L}}$. For a closed integral subscheme $Z$ of $X$ of dimension
$d$, with Zariski closure $\mathcal{Z}$ in $\mathcal{X}$, of dimension $d + 1$, put
$\deg_L(Z) = \deg(c_1(L)^d \mid Z)$; when $\deg_L(Z) \ne 0$, which holds for every $Z$ when $L$ is
ample, the normalized height is
$$h^{\mathrm{norm}}_{\bar{\mathcal{L}}}(Z) =
\frac{\widehat{\deg}\bigl( \hat c_1(\bar{\mathcal{L}})^{d+1} \mid \mathcal{Z} \bigr)}
{(d + 1) \deg_L(Z)} = \frac{h_{\bar{\mathcal{L}}}(\mathcal{Z})}{(d + 1) \deg_L(Z)}.$$
Chambert-Loir writes $h_{\bar{\mathcal{L}}}(Z)$ for this normalized height; the unnormalized height
$h_{\bar{\mathcal{L}}}(\mathcal{Z})$ of Bost, Gillet and Soulé is a different number. The function
$x \mapsto h^{\mathrm{norm}}_{\bar{\mathcal{L}}}([x])$ on $X(\overline{\mathbb{Q}})$, where $[x]$ is
the Zariski closure of $x$ in $X$, is a height function relative to $L$ in the sense of Weil.
If $f \colon \mathcal{X}' \to \mathcal{X}$ is a generically finite morphism of proper flat schemes
over $\mathbb{Z}$, $L$ is ample, and $Z$ is a closed integral subscheme of $\mathcal{X}'_\mathbb{Q}$
with $\dim f(Z) = \dim Z$, then $\deg_{f^*L}(Z) > 0$ and $h^{\mathrm{norm}}_{f^*
\bar{\mathcal{L}}}(Z) = h^{\mathrm{norm}}_{\bar{\mathcal{L}}}(f(Z))$.

On $\mathbb{P}^N_\mathbb{Z}$, give $\mathcal{O}(1)$ the Fubini–Study metric: if $s_f$ is the
section defined by a homogeneous linear form $f$ in $T_0, \dots, T_N$ and
$x = [x_0 : \dots : x_N] \in \mathbb{P}^N(\mathbb{C})$, then $\lVert s_f \rVert(x) =
|f(x_0, \dots, x_N)| / (|x_0|^2 + \dots + |x_N|^2)^{1/2}$. The height
$h_{\overline{\mathcal{O}(1)}}$ of cycles of $\mathbb{P}^N_\mathbb{Z}$ for this metric is the height
introduced by Faltings.

## Depends on

- [Arithmetic degree and arithmetic intersection numbers](arithmetic-intersection-numbers.md), for the arithmetic degrees $\widehat{\deg}(\hat c_1(\bar L)^p \mid Z)$
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)

## Sources

- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms",
  J. Amer. Math. Soc. 7 (1994), 903–1027,
  <https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/>: introduction,
  definition (3.1.1), p. 945 ("For any cycle $Z \in Z_p(X)$ we define the height of $Z$ with
  respect to $\bar L$ to be the real number $h_{\bar L}(Z) = \widehat{\deg}(\hat c_1(\bar L)^p \mid
  Z)$", $Z_p(X)$ being the cycles of dimension $p$ on the arithmetic variety $X$), and 3.1.2.3
  (Faltings's height, from G. Faltings, "Diophantine approximation on abelian varieties", Ann. of
  Math. (2) 133 (1991), 549–576).
- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: Theorem (2.5) and Examples (2.7)
  and (2.8), pp. 3–4; Definition (3.3), Proposition (3.4), p. 5, and Example (3.5), p. 6; Definition
  (5.2) (the metric on $\mathcal{O}(1)$), p. 12.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses heights of cycles, with their recursive characterization and projection formula, as `GlobalTheory.Published.CycleHeights`.

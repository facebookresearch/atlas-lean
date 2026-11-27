# Arithmetic degree and arithmetic intersection numbers

Let $X$ be an arithmetic variety over an arithmetic ring $(A, \Sigma, F_\infty)$ with smooth
quasi-projective generic fibre, and assume that $X$ is regular and irreducible. The arithmetic Chow
group $\widehat{CH}^1(X)$ sits in an exact sequence

$$\Gamma(X, \mathcal{O}_X)^\times \xrightarrow{\ \rho\ } C^\infty(X_\infty, \mathbb{R})^{F_\infty}
\xrightarrow{\ a\ } \widehat{CH}^1(X) \xrightarrow{\ \zeta\ } CH^1(X) \to 0, \qquad
\rho(u) = -\log |u|^2,$$

where $C^\infty(X_\infty, \mathbb{R})^{F_\infty}$ is the space of real smooth functions on
$X_\infty$ invariant under $F_\infty$: a function is killed by $a$ exactly when it is $-\log |u|^2$
for a global unit $u$, whose arithmetic divisor is $(0, -\log |u|^2)$. When $\Gamma(X,
\mathcal{O}_X) = A$, for instance for $X = \operatorname{Spec} A$, the first group is $A^\times$; in
general it is larger: for $A = \mathbb{Z}$ and $X = \operatorname{Spec}
\mathcal{O}_{\mathbb{Q}(\sqrt 2)}$ the unit $1 + \sqrt 2$ gives a nonzero function, while
$\mathbb{Z}^\times = \{\pm 1\}$ gives $0$. If moreover $X$ is projective over $A$, then
$\widehat{CH}^1(X)$ is canonically isomorphic to the group $\widehat{\mathrm{Pic}}(X)$ of isometry
classes of hermitian line bundles, $\bar L$ corresponding to $\hat c_1(\bar L) =
[(\operatorname{div}(s), -\log \lVert s \rVert^2)]$ for any rational section $s$ of $L$ not
identically zero.

For $X = \operatorname{Spec} A$ the sequence reads $A^\times \to (\bigoplus_{\sigma \in \Sigma}
\mathbb{R})^{F_\infty} \to \widehat{CH}^1(\operatorname{Spec} A) \to CH^1(\operatorname{Spec} A) \to
0$, and $CH^1(\operatorname{Spec} A)$ is the ideal class group when $A$ is a Dedekind domain. For
the ring of integers $\mathcal{O}_K$ of a number field $K$, with $\Sigma$ the set of all embeddings,
the arithmetic degree is the homomorphism

$$\widehat{\deg} \colon \widehat{CH}^1(\operatorname{Spec} \mathcal{O}_K) \to \mathbb{R}, \qquad
\Bigl( \sum_i n_i [\mathfrak{p}_i], (g_\sigma)_{\sigma \in \Sigma} \Bigr) \mapsto
\sum_i n_i \log \#(\mathcal{O}_K / \mathfrak{p}_i) + \frac{1}{2} \sum_{\sigma \in \Sigma}
g_\sigma,$$

without division by $[K : \mathbb{Q}]$. It vanishes on **principal** arithmetic divisors
$\widehat{\operatorname{div}}(f)$: for $K = \mathbb{Q}$ and $f = 2$, $\log 2 + \frac12 (-\log 4) =
0$; it does not vanish on all arithmetic divisors, the class of $([2], 0)$ having degree $\log 2$.
For $A = \mathbb{Z}$ it is an isomorphism $\widehat{CH}^1(\operatorname{Spec} \mathbb{Z}) \cong
\mathbb{R}$, because $\mathbb{Z}^\times$ is finite and $\mathbb{Z}$ has trivial class group.

Let $\pi \colon X \to S$ be a proper morphism of equidimensional arithmetic varieties over $A$,
separated and of finite Krull dimension, with smooth quasi-projective generic fibres, whose
restriction $X_F \to S_F$ is smooth, and let $d = \dim X - \dim S$. The push-forward $\pi_*(Z, g) =
(\pi_* Z, \pi_* g)$ of cycles and currents defines a homomorphism $\pi_* \colon \widehat{CH}^p(X)
\to \widehat{CH}^{p-d}(S)$. If moreover $X$ and $S$ are regular and $p + q = d + 1$, composing the
intersection product with $\pi_*$ gives a pairing

$$\langle \cdot, \cdot \rangle \colon \widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to
\widehat{CH}^1(S)_\mathbb{Q}, \qquad \langle \alpha, \beta \rangle = \pi_*(\alpha\beta),$$

and there is a bi-additive pairing $\widehat{CH}^p(X) \times \widehat{CH}^q(X) \to
\widehat{CH}^1(S)$ that induces it; this integral lift is a separate theorem, not the push-forward
of an integral product. When $X$ is a regular arithmetic variety projective over $\mathbb{Z}$ of
dimension $d + 1$, so that $X_\mathbb{Q}$ has dimension $d$, composing with $\widehat{\deg}$ gives a
real-valued pairing for $p + q = d + 1$. For hermitian line bundles $\bar L_1, \dots, \bar L_{d+1}$
on such an $X$, the product $\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_{d+1})$ lies in
$\widehat{CH}^{d+1}(X)$, products with classes of codimension one being defined without
denominators, and their arithmetic intersection number is

$$(\bar L_1 \cdots \bar L_{d+1}) = \widehat{\deg}\, \pi_*\bigl( \hat c_1(\bar L_1) \cdots
\hat c_1(\bar L_{d+1}) \bigr), \qquad \pi \colon X \to \operatorname{Spec} \mathbb{Z},$$

written $(\bar L^{d+1})$ when all the $\bar L_i$ equal $\bar L$.

**Chambert-Loir's characterization.** Let $X$ be a proper flat scheme over $\mathbb{Z}$, with
hermitian metrics in Chambert-Loir's sense, let $n = \dim X$, $Z_k(X)$ the group of $k$-dimensional
cycles, and $\bar L_1, \dots, \bar L_n$ hermitian line bundles on $X$. There is a unique family of
linear maps $\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid \cdot) \colon Z_k(X)
\to \mathbb{R}$, $0 \le k \le n$, such that $\widehat{\deg}(z) = \log \# \kappa(z)$ for every closed
point $z$, and such that for every integral closed subscheme $Z$ of dimension $k \ge 1$, every
integer $m \ne 0$ and every regular meromorphic section $s$ of $L_k^{\otimes m}|_Z$, that is, a
section over a dense open subscheme of $Z$ that is not zero there,

$$m \, \widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid Z \bigr) =
\widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_{k-1}) \mid \operatorname{div}(s)
\bigr) + \int_{Z(\mathbb{C})} \log \lVert s \rVert^{-1} \, c_1(\bar L_1) \cdots c_1(\bar L_{k-1}),$$

with the metric of $\bar L_k^{\otimes m}$ on $s$. For each $k$ the map is multilinear and symmetric
in the $k$ entries $\bar L_1, \dots, \bar L_k$ and depends only on their classes in
$\widehat{\mathrm{Pic}}(X)$. The following hold.

1. *Comparison.* If $X$ is regular and projective, the setting of Gillet and Soulé's number, and the
   metrics are invariant under complex conjugation, $\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat
   c_1(\bar L_n) \mid X)$ is the number of Gillet and Soulé defined above. Still with invariant
   metrics on a projective arithmetic model (more generally a model of Bost, Gillet and Soulé, with
   proper cycle support), regularity of the generic fibre suffices: Bost, Gillet and Soulé then
   define the corresponding numbers through the action of first Chern classes on arithmetic Chow
   groups graded by dimension.
2. *Change of metric.* If $\bar L_k' = (L_k, e^{-u} \lVert \cdot \rVert)$ for a real smooth function
   $u$ on $X(\mathbb{C})$, applying the recursion to the same section $s$ gives

    $$\widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_{k-1}) \hat c_1(\bar L_k') \mid Z
    \bigr) = \widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid Z \bigr) +
    \int_{Z(\mathbb{C})} u \, c_1(\bar L_1) \cdots c_1(\bar L_{k-1}),$$

   and by symmetry the same holds in each entry. For a constant $u = t$ the integral is $t
   \deg(c_1(L_1) \cdots c_1(L_{k-1}) \mid Z_\mathbb{Q})$ by the
   [comparison of geometric degrees with integrals of Chern forms](geometric-degrees-as-integrals-of-chern-forms.md);
   in particular, replacing the metric of $\bar L$ by $e^{-t} \lVert \cdot \rVert$ adds $(d + 1) t
   \deg(L_\mathbb{Q}^d)$ to $(\bar L^{d+1})$ on $X$ of dimension $d + 1$. In Gillet and Soulé's
   normalization, with the Green function $-\log \lVert s \rVert^2$, this rescaling changes the
   Green function by $2t$.
3. *Projection formula.* Let $f \colon X' \to X$ be either a generically finite morphism of proper
   flat schemes over $\mathbb{Z}$, with metrics in Chambert-Loir's sense (Chambert-Loir, Proposition
   (2.9)), or a morphism of projective arithmetic varieties over $\mathcal{O}_K$ with regular
   generic fibres, regular or not, with metrics invariant under complex conjugation (Bost, Gillet
   and Soulé, Propositions 2.3.1 (iv) and 3.2.1 (iii) with the remarks after them), and let $Z
   \subseteq X'$ be an integral closed subscheme of dimension $k$. Then $\widehat{\deg}(\hat c_1(f^*
   \bar L_1) \cdots \hat c_1(f^* \bar L_k) \mid Z)$ is $0$ if $\dim f(Z) < k$, and equals
   $[\kappa(Z) : \kappa(f(Z))] \, \widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid
   f(Z))$ otherwise, that is, when $Z \to f(Z)$ is generically finite. No degree factor is lost for
   these unnormalized numbers.
4. *Birational invariance.* For every proper birational morphism $f \colon Z' \to Z$ of integral
   proper flat schemes over $\mathbb{Z}$ with $Z'_\mathbb{Q}$ regular, and $k = \dim Z = \dim Z'$,
   $\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid Z) = \widehat{\deg}(\hat
   c_1(f^* \bar L_1) \cdots \hat c_1(f^* \bar L_k) \mid Z')$.

For an arithmetic variety $X$ of dimension $d + 1$ in the sense of Zhang, Moriwaki and Yuan
(integral, projective and flat over $\mathbb{Z}$), whose generic fibre may be singular, Zhang
defines the self-intersection $(\bar L^{d+1})$ as $(\mu^* \bar L)^{d+1}$ for a generic resolution of
singularities $\mu \colon X' \to X$ (§1.2, p. 189), and Yuan the mixed numbers $(\bar L_1 \cdots
\bar L_{d+1})$ as $(\mu^* \bar L_1 \cdots \mu^* \bar L_{d+1})$ (§2.1, p. 8); it does not depend on
the choice of $\mu$, because two generic resolutions are dominated by a third and the projection
formula applies.

## Depends on

- [Arithmetic intersection product](arithmetic-intersection-product.md)
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)
- [Geometric degrees as integrals of first Chern forms](geometric-degrees-as-integrals-of-chern-forms.md), for the effect of a constant rescaling of a metric in item 2
- [Arithmetic Chow groups](arithmetic-chow-group.md), for the arithmetic Chow groups and the maps
  $a$ and $\zeta$

## Proof depends on

- [Chow groups with supports and their products](chow-groups-with-supports.md), for the integral lift of the intersection pairing (Gillet–Soulé, proof of Theorem 4.3.2, pp. 148–151)
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolutions through which the intersection numbers are defined when $X_\mathbb{Q}$ is singular and for a common refinement of two of them

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: the Theorem after 3.3.5, exact sequence (i)
  for $p = 1$ (global units), p. 128; 3.4.2 ($\widehat{CH}^1$ and hermitian line bundles, announcing
  the isomorphism with $\widehat{\mathrm{Pic}}(X)$ proved in their "Characteristic classes" paper,
  Proposition 2.5; the shortcut to $A^\times$ printed there needs $\Gamma(X, \mathcal{O}_X) = A$),
  3.4.3 (the arithmetic degree and $\widehat{CH}^1(\operatorname{Spec} \mathbb{Z}) \cong
  \mathbb{R}$), p. 131; Theorem 3.6.1 (ii) (push-forward, pp. 134–136); 4.3.1 and Theorem 4.3.2
  (intersection pairings and numbers, p. 147, proved pp. 148–151). In 3.4.3 the formula $\#(Z) =
  \sum n_i \#(\mathcal{O}_F / \mathfrak{p}_i)$ is a misprint for $\log \#(Z) = \sum n_i \log
  \#(\mathcal{O}_F / \mathfrak{p}_i)$.
- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027, archived publisher scan
  <https://web.archive.org/web/20170815232351id_/https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/S0894-0347-1994-1260106-X.pdf>:
  §2.1.2, p. 932 ($\hat c_1(\bar L) = [(\operatorname{div} s, -\log \lVert s \rVert^2)]$); (2.3.16),
  p. 944, and §3.1.2.2, pp. 946–947 (the arithmetic degree with $\log \mathrm{N}\mathfrak{p}$;
  (2.1.8), p. 934, prints it without the logarithm); Proposition 2.3.1 and §2.3.1, Remark (ii), pp.
  937–942; Proposition 3.2.1 (iii), formula (3.2.1), and the Remark that follows, p. 949.
- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: the exact sequence (2.3.1), p. 3;
  Theorem (2.5) with (2.5.1)–(2.5.2), pp. 3–4; Proposition (2.9), pp. 4–5; Remark (2.10), p. 5.
- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: §1.2, p. 189 (intersection numbers
  through generic resolutions and their independence).
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Section 2.1, p. 8.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses these numbers, with their existence, recursion, change of metric, constant rescaling and
  projection formula, as `GlobalTheory.Published.ArCalc`, and their invariance under birational
  morphisms of generically smooth arithmetic varieties, together with the expression of geometric
  degrees as integrals of Chern forms, as `GlobalTheory.Published.ArDegree`; these are formulations
  for the library's own models, related to, not literally equal to, the statements above.

# Arithmetic degree and arithmetic intersection numbers

Let $X$ be an arithmetic variety over an arithmetic ring $(A, \Sigma, F_\infty)$, regular,
irreducible and projective over $A$. The arithmetic Chow group $\widehat{CH}^1(X)$ sits in an
exact sequence
$$A^\times \to C^\infty(X_\infty, \mathbb{R})^{F_\infty} \xrightarrow{a} \widehat{CH}^1(X)
\xrightarrow{\zeta} CH^1(X) \to 0,$$
in which the image of the first map consists of the functions equal to $\log |\sigma(u)|^2$ on
$X_\sigma(\mathbb{C})$ for $\sigma \in \Sigma$, with $u \in A^\times$. Moreover $\widehat{CH}^1(X)$
is canonically isomorphic to the group $\widehat{\mathrm{Pic}}(X)$ of isometry classes of hermitian
line bundles; $\hat c_1(\bar L) \in \widehat{CH}^1(X)$ denotes the class corresponding to $\bar L$.

For $X = \operatorname{Spec} A$ the sequence reads $A^\times \to (\bigoplus_{\sigma \in \Sigma}
\mathbb{R})^{F_\infty} \to \widehat{CH}^1(\operatorname{Spec} A) \to CH^1(\operatorname{Spec} A) \to
0$, and $CH^1(\operatorname{Spec} A)$ is the ideal class group when $A$ is a Dedekind domain. For
the ring of integers $\mathcal{O}_K$ of a number field $K$, the arithmetic degree is the
homomorphism
$$\widehat{\deg} \colon \widehat{CH}^1(\operatorname{Spec} \mathcal{O}_K) \to \mathbb{R}, \qquad
\Bigl( \sum_i n_i [\mathfrak{p}_i], (g_\sigma)_{\sigma \in \Sigma} \Bigr) \mapsto
\sum_i n_i \log \#(\mathcal{O}_K / \mathfrak{p}_i) + \frac{1}{2} \sum_{\sigma \in \Sigma}
g_\sigma,$$
and for $A = \mathbb{Z}$ it is an isomorphism $\widehat{CH}^1(\operatorname{Spec} \mathbb{Z}) \cong
\mathbb{R}$, because $\mathbb{Z}^\times$ is finite and $\mathbb{Z}$ has trivial class group.

Let $\pi \colon X \to S$ be a proper morphism of equidimensional arithmetic varieties over $A$ whose
restriction $X_F \to S_F$ to the generic fibres is smooth, and let $d = \dim X - \dim S$. The
push-forward $\pi_*(Z, g) = (\pi_* Z, \pi_* g)$ of cycles and currents defines a homomorphism
$\pi_* \colon \widehat{CH}^p(X) \to \widehat{CH}^{p-d}(S)$. If moreover $X$ and $S$ are regular and
$p + q = d + 1$, composing the intersection product with $\pi_*$ gives a pairing
$$\langle \cdot, \cdot \rangle \colon \widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to
\widehat{CH}^1(S)_\mathbb{Q}, \qquad \langle \alpha, \beta \rangle = \pi_*(\alpha\beta),$$
and there is a bi-additive pairing $\widehat{CH}^p(X) \times \widehat{CH}^q(X) \to
\widehat{CH}^1(S)$ that induces it. When $X$ is a regular arithmetic variety projective over
$\mathbb{Z}$ of dimension $d + 1$, so that $X_\mathbb{Q}$ has dimension $d$, composing with
$\widehat{\deg}$ gives a real-valued pairing $\widehat{CH}^p(X) \otimes \widehat{CH}^q(X) \to
\mathbb{R}$ for $p + q = d + 1$. For hermitian line bundles $\bar L_1, \dots, \bar L_{d+1}$ on such
an $X$, the product $\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_{d+1})$ lies in
$\widehat{CH}^{d+1}(X)$, products with classes of codimension one being defined without
denominators, and their arithmetic intersection number is
$$(\bar L_1 \cdots \bar L_{d+1}) = \widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots
\hat c_1(\bar L_{d+1}) \bigr) = \widehat{\deg}\, \pi_*\bigl( \hat c_1(\bar L_1) \cdots
\hat c_1(\bar L_{d+1}) \bigr), \qquad \pi \colon X \to \operatorname{Spec} \mathbb{Z},$$
written $(\bar L^{d+1})$ when all the $\bar L_i$ equal $\bar L$.

Chambert-Loir characterizes these numbers on any proper flat scheme $X$ over $\mathbb{Z}$, with
hermitian metrics in his sense. Let $n = \dim X$, let $Z_k(X)$ be the group of $k$-dimensional
cycles, and let $\bar L_1, \dots, \bar L_n$ be hermitian line bundles on $X$. There is a unique
family of linear maps $\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid \cdot)
\colon Z_k(X) \to \mathbb{R}$, $0 \le k \le n$, such that $\widehat{\deg}(z) = \log \# \kappa(z)$
for every closed point $z$, and such that for every integral closed subscheme $Z$ of dimension
$k \ge 1$, every integer $m \ne 0$ and every meromorphic section $s$ of $L_k^{\otimes m}|_Z$ defined
on a dense open subscheme of $Z$,
$$m \, \widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid Z \bigr) =
\widehat{\deg}\bigl( \hat c_1(\bar L_1) \cdots \hat c_1(\bar L_{k-1}) \mid \operatorname{div}(s)
\bigr) + \int_{Z(\mathbb{C})} \log \lVert s \rVert^{-1} \, c_1(\bar L_1) \cdots c_1(\bar L_{k-1}).$$
These maps are multilinear and symmetric in $\bar L_1, \dots, \bar L_n$ and depend only on their
classes in $\widehat{\mathrm{Pic}}(X)$. When $X$ is regular, $\widehat{\deg}(\hat c_1(\bar L_1)
\cdots \hat c_1(\bar L_n) \mid X)$ is the number defined above by Gillet and Soulé; products of
classes $\hat c_1(\bar L)$ can already be defined when only $X_\mathbb{Q}$ is regular. For every
birational morphism $f \colon Z' \to Z$ with $Z'_\mathbb{Q}$ regular,
$\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid Z) =
\widehat{\deg}(\hat c_1(f^* \bar L_1) \cdots \hat c_1(f^* \bar L_k) \mid Z')$. If
$f \colon X' \to X$ is a generically finite morphism of proper flat schemes over $\mathbb{Z}$ and
$Z \subseteq X'$ is integral of dimension $k$, then
$\widehat{\deg}(\hat c_1(f^* \bar L_1) \cdots \hat c_1(f^* \bar L_k) \mid Z)$ is $0$ if
$\dim f(Z) < k$ and equals $\widehat{\deg}(\hat c_1(\bar L_1) \cdots \hat c_1(\bar L_k) \mid
f_* Z)$ otherwise, where $f_* Z = [\kappa(Z) : \kappa(f(Z))] \, f(Z)$.

For an arithmetic variety $X$ of dimension $d + 1$ in the sense of Zhang, Moriwaki and Yuan, whose
generic fibre may be singular, $(\bar L_1 \cdots \bar L_{d+1})$ is defined as
$(\mu^* \bar L_1 \cdots \mu^* \bar L_{d+1})$ for a generic resolution of singularities
$\mu \colon X' \to X$; it does not depend on the choice of $\mu$.

## Depends on

- [Arithmetic intersection product](arithmetic-intersection-product.md)
- [Arithmetic varieties and hermitian vector bundles](arithmetic-variety.md)
- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolution through which the intersection numbers are defined when $X_\mathbb{Q}$ is singular (Yuan, Section 2.1)

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 3.4.2 ($\widehat{CH}^1$ and hermitian line
  bundles, announcing the isomorphism with $\widehat{\mathrm{Pic}}(X)$ proved in their
  "Characteristic classes" paper, Proposition 2.5), 3.4.3 (the arithmetic degree and
  $\widehat{CH}^1(\operatorname{Spec} \mathbb{Z}) \cong \mathbb{R}$), p. 131; Theorem 3.6.1 (ii)
  (push-forward, pp. 134–136); 4.3.1 and Theorem 4.3.2 (intersection pairings and numbers,
  p. 147). In 3.4.3 the formula $\#(Z) = \sum n_i \#(\mathcal{O}_F / \mathfrak{p}_i)$ is a misprint
  for $\log \#(Z) = \sum n_i \log \#(\mathcal{O}_F / \mathfrak{p}_i)$.
- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), <https://arxiv.org/abs/1904.05630v3>: Theorem (2.5), pp. 3–4,
  Proposition (2.9), pp. 4–5, and Remark (2.10), p. 5.
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Section 2.1, p. 8
  (intersection numbers through a generic resolution, independent of its choice, after Zhang).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses these numbers, with their recursive characterization, change of metric and projection formula, as `GlobalTheory.Published.ArCalc`, and their invariance under birational morphisms of generically smooth arithmetic varieties, together with the expression of geometric degrees as integrals of Chern forms, as `GlobalTheory.Published.ArDegree`.

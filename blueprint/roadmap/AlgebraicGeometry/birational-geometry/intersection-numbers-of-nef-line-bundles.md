# Intersection numbers and Riemann–Roch for nef line bundles

This node is still to be broken down: the statements are precise, but their proofs are not. Let $X$
be a projective scheme of dimension $n$ over an algebraically closed field $k$ of arbitrary
characteristic, not necessarily reduced or irreducible; a line bundle is nef if its degree on every
integral proper curve in $X$ is nonnegative.

1. (Kleiman.) If $L_1, \dots, L_n$ are nef line bundles on $X$, possibly different, then $(L_1
   \cdots L_n) \ge 0$, the intersection number being taken against the structure sheaf of $X$.
2. If $X$ is integral and $L$ is nef, then $L$ is big if and only if $(L^n) > 0$.
3. If $L$ is nef, then $h^0(X, L^{\otimes m}) = \frac{(L^n)}{n!} m^n + O(m^{n-1})$ as $m \to
   \infty$.
4. (The form of 3 used by Alpöge's library for coordinate rings, an unsourced target in this form.)
   This item has its own data, not the $k$ and $X$ of 1–3: a field $\Omega$ of characteristic zero
   and a finite family $y = (y_{k,i})$ of elements of $\Omega$, in blocks $k \in K$, presenting an
   arithmetic variety $X$ of dimension $D + 1$ in $\prod_k \mathbb{P}^{|\iota(k)| - 1}_\mathbb{Z}$
   by its multihomogeneous coordinate ideal, with the presentation **birational**: every element of
   $\Omega$ is a ratio $g(y)/h(y)$, $h(y) \ne 0$, of integral multihomogeneous polynomials of the
   **same** multidegree, as in the setting of
   [small sections and coordinate lattices](../arakelov-geometry/arithmetic-volumes/small-sections-and-coordinate-lattices.md).
   Let $a \in \mathbb{Z}^K$, with entries of any sign, be nef on the generic fibre: the generic
   degree of $a$ on the closure of every curve of $X_\mathbb{Q}$ is nonnegative. For a chart $c$, a
   choice of $c(k)$ with all $y_{k,c(k)} \ne 0$, let $R_c = \mathbb{Z}[y_{k,i}/y_{k,c(k)}] \subset
   \Omega$, and for $\tau \ge 0$ let $V_\tau \subset \Omega$ be the $\mathbb{Q}$-span of the group
   of $s \in \Omega$ such that $s \prod_k y_{k,c(k)}^{-\tau a_k}$ is integral over $R_c$ for every
   chart $c$ (the library's normalized chart lattice `chartLatNm`). Then **every** $V_\tau$ is
   finite-dimensional, and $D! \dim_\mathbb{Q}(V_\tau) / \tau^D$ converges to the generic degree
   $(a^D)$ as $\tau \to \infty$. The element $s$ is tested only after dividing by the chart monomial
   of multidegree $\tau a$: for $X = \mathbb{P}^1_\mathbb{Z}$, $y = (1, t)$ in $\Omega =
   \mathbb{Q}(t)$ and $a = 1$, testing $s$ itself on the two charts gives $\mathbb{Z}[t] \cap
   \mathbb{Z}[t^{-1}] = \mathbb{Z}$, of rank $1$ in every degree, whereas the condition $s \in
   \mathbb{Z}[t]$, $s/t^\tau \in \mathbb{Z}[t^{-1}]$ gives $V_\tau = \langle 1, t, \dots, t^\tau
   \rangle$, of dimension $\tau + 1$. The span is needed: the elements of $V_\tau$, such as $1/2$,
   need not be integral.
5. (Projection formula, over any field.) If $f \colon X' \to X$ is a morphism of proper schemes over
   a field, $L_1, \dots, L_e$ are line bundles on $X$ and $Z \subset X'$ is an integral closed
   subscheme of dimension $e$, then $(f^* L_1 \cdots f^* L_e \cdot Z) = [\kappa(Z) : \kappa(f(Z))]\,
   (L_1 \cdots L_e \cdot f(Z))$ if $\dim f(Z) = e$, and $0$ otherwise.
Item 5 follows from $f_*(c_1(f^* L) \cap \alpha) = c_1(L) \cap f_* \alpha$ for proper $f$ and every
cycle $\alpha$ (Stacks Project, Tag 02SU), applied to each factor, and the preservation of degrees
of zero-cycles by proper push-forward. The $m^n$ coefficient in 3 is $(L^n)/n!$, which may vanish;
it is the coefficient of $m^n$, not necessarily the leading coefficient. For a coherent sheaf
$\mathcal{F} \ne 0$ with support of dimension $e$, $\chi(X, \mathcal{F} \otimes L^{\otimes m})$ is a
polynomial of degree at most $e$ whose $m^e$ coefficient is $\sum_Z
\operatorname{length}(\mathcal{F}_{\eta_Z}) (L^e \cdot Z)/e!$, over the $e$-dimensional integral
components $Z$ of the support, with generic points $\eta_Z$: for $X = \mathbb{P}^2$, $L =
\mathcal{O}(1)$ and $\mathcal{F}$ the structure sheaf of a line, $\chi = m + 1$. Item 4 differs from
3 in the spaces it counts, which are $\mathbb{Q}$-spans of groups of elements of a fixed field
defined by integrality after a chart trivialization, not the global sections of a power of one line
bundle on the generic fibre, and in its conclusion, a limit with no error term. Over an
algebraically closed field of characteristic zero and for smooth $X$, item 2 is Esnault and
Viehweg's Lemma 5.8 a), and for compact Kähler manifolds an analytic form of 2 and 3, with a weaker
asymptotic, is stated with the [volume of a line bundle](volume-of-a-line-bundle.md).

A good expansion has pages for: 1, by the ampleness of $A \otimes L_i^{\otimes r}$ for an ample $A$,
every nef $L_i$ and $r \ge 0$ (Keeler, Proposition 2.13), the positivity of intersection numbers of
ample line bundles and the multilinearity of intersection numbers (Stacks Project, Tags 0BEV and
0BER), expanding $\prod_i (A + r L_i)$ divided by $r^n$ as $r \to \infty$; 2, as Birkar proves it
over any field (Theorem 1.5, with its proof on p. 13 by Fujita vanishing, asymptotic Riemann–Roch,
the restriction sequence of an ample divisor and induction on the dimension, and the criterion for
bigness by growth of sections of Lemma 4.2); the Riemann–Roch polynomial of a coherent sheaf above,
with its $m^e$ coefficient (Stacks Project, Tags 0BEM, 0BEN and 0BEP); the bound $h^i(X, \mathcal{F}
\otimes L^{\otimes m}) = O(m^{e-1})$ for $i > 0$, nef $L$ and coherent $\mathcal{F}$ with support of
dimension $e$ (Birkar, Proposition 4.3), proved with Fujita's vanishing theorem in the uniform form
of Keeler's Theorem 1.5 (for a fixed ample $A$, $H^i(\mathcal{F} \otimes A^{\otimes t} \otimes N) =
0$ for $i > 0$, all large $t$ and every nef $N$) and induction on hyperplane sections avoiding the
associated points of $\mathcal{F}$; and, for 4, a squeeze between section spaces on the generic
fibre. The $\mathbb{Q}$-span of the group of $s$ with $s \prod_k y_{k,c(k)}^{-\tau a_k} \in R_c$ on
every chart is $H^0(X_\mathbb{Q}, \mathcal{O}(\tau a))$ and lies in $V_\tau$; one nonzero multiplier
$c \in \Omega$ and one shift $e \in \mathbb{N}^K$, fixed independently of $\tau$, give $c V_\tau
\subset H^0(X_\mathbb{Q}, \mathcal{O}(\tau a + e))$, hence the finite dimensionality. The Euler
polynomials of the invertible sheaves $\mathcal{F} = \mathcal{O}$ and $\mathcal{F} = \mathcal{O}(e)$
twisted by $\mathcal{O}(\tau a)$, with the bounds on their higher cohomology, have the same $\tau^D$
coefficient $(a^D)/D!$, as $\mathcal{F}$ has rank one at every generic point; they are applied after
flat base change from $\mathbb{Q}$ to an algebraic closure, which preserves the dimensions of the
section spaces, and over which $X_\mathbb{Q}$ need not stay integral. The case $D = 0$ is treated
separately. Item 3 alone does not suffice, as it concerns untwisted powers of one line bundle over
an algebraically closed field.

## Depends on

- [Nef and big line bundles](nef-and-big-line-bundles.md)
- [Small sections and lattices of homogeneous coordinate rings](../arakelov-geometry/arithmetic-volumes/small-sections-and-coordinate-lattices.md),
  for the coordinate presentations, charts and chart groups of 4

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for the Euler polynomial of a coherent sheaf and flat base change, used in the squeeze for 4
## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Lemma 5.7 and Lemma 5.8 with its proof, pp. 46–47.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Lemma 2.1, p. 10.
- D. S. Keeler, "Ample filters of invertible sheaves", arXiv:math/0108068 (version 5): Theorem 1.5,
  p. 3 (with the erratum E2.5); Definition 2.9 and Propositions 2.10 and 2.13, pp. 5–6.
- C. Birkar, "The augmented base locus of real divisors over arbitrary fields", arXiv:1312.0239
  (version 1): Theorem 1.5, p. 3, with its proof, p. 13; §§2.5–2.6; Lemmas 4.1–4.2 and Proposition
  4.3, pp. 7–10.
- The Stacks Project, <https://stacks.math.columbia.edu>: Tags 0BEM, 0BEN, 0BEP (numerical
  polynomials and intersection numbers of coherent sheaves), 0BER (multilinearity), 0BEV (positivity
  for ample line bundles) and 02SU (projection formula for first Chern classes).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1–3 in this form as `GlobalTheory.Published.NefNumerics` (the conjunction of
  `NefProductNonneg`, `NefBigIff` and `NefRiemannRoch`; only the second assumes $X$ integral), and 4
  as `GlobalTheory.CompanionTheory.Ar.Pub.NefRR`, with the spans of `chartLatNm`; no published
  source stating 4 has been identified.

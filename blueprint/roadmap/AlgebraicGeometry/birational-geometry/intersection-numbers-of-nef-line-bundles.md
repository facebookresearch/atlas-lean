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
   Let $\Omega$ be a field of characteristic zero and $y$ a finite family of elements of $\Omega$,
   grouped into blocks, generating the function field of the generic fibre $X_\mathbb{Q}$ of an
   arithmetic variety of dimension $D + 1$ embedded in a product of projective spaces by its
   multihomogeneous coordinate ideal, and let $a$ be a multidegree nef on $X_\mathbb{Q}$. For $\tau
   \ge 0$, let $V_\tau \subset \Omega$ be the $\mathbb{Q}$-span of the elements of multidegree $\tau
   a$ that are integral over every chart ring of $X$ (the library's normalized chart lattice
   `chartLatNm`). Then **every** $V_\tau$ is finite-dimensional, and $D! \dim_\mathbb{Q}(V_\tau) /
   \tau^D$ converges to the generic degree $(a^D)$ as $\tau \to \infty$.

The $m^n$ coefficient in 3 is $(L^n)/n!$, which may vanish; it is the coefficient of $m^n$, not
necessarily the leading coefficient. For a coherent sheaf $\mathcal{F} \ne 0$ with support of
dimension $e$, $\chi(X, \mathcal{F} \otimes L^{\otimes m})$ is a polynomial of degree at most $e$
whose $m^e$ coefficient is $\sum_Z \operatorname{length}(\mathcal{F}_{\eta_Z}) (L^e \cdot Z)/e!$,
over the $e$-dimensional integral components $Z$ of the support, with generic points $\eta_Z$: for
$X = \mathbb{P}^2$, $L = \mathcal{O}(1)$ and $\mathcal{F}$ the structure sheaf of a line, $\chi = m +
1$. Item 4 differs from 3 in the spaces it counts, which are $\mathbb{Q}$-spans of elements of a
fixed field, integral over the chart rings, not the global sections of $L^{\otimes m}$ on the
generic fibre, and in its conclusion, a limit with no error term. Over an algebraically closed field
of characteristic zero and for smooth $X$, item 2 is Esnault and Viehweg's Lemma 5.8 a), and for
compact Kähler manifolds an analytic form of 2 and 3, with a weaker asymptotic, is stated with the
[volume of a line bundle](volume-of-a-line-bundle.md).

A good expansion has pages for: 1, by the ampleness of $A \otimes L_i^{\otimes r}$ for an ample $A$,
every nef $L_i$ and $r \ge 0$ (Keeler, Proposition 2.13), the positivity of intersection numbers of
ample line bundles and the multilinearity of intersection numbers (Stacks Project, Tags 0BEV and
0BER), expanding $\prod_i (A + r L_i)$ divided by $r^n$ as $r \to \infty$; 2, through the augmented
base locus (Birkar, Theorem 1.5 and Lemma 4.2, over any field); the Riemann–Roch polynomial of a
coherent sheaf above, with its $m^e$ coefficient (Stacks Project, Tags 0BEM, 0BEN and 0BEP); the
bound $h^i(X, \mathcal{F} \otimes L^{\otimes m}) = O(m^{e-1})$ for $i > 0$, nef $L$ and coherent
$\mathcal{F}$ with support of dimension $e$ (Birkar, Proposition 4.3), proved with Fujita's
vanishing theorem in the uniform form of Keeler's Theorem 1.5 (for a fixed ample $A$,
$H^i(\mathcal{F} \otimes A^{\otimes t} \otimes N) = 0$ for $i > 0$, all large $t$ and every nef $N$)
and induction on hyperplane sections avoiding the associated points of $\mathcal{F}$; and, for 4, a
comparison of $V_\tau$ with the sections of $L^{\otimes \tau}$ on $X_\mathbb{Q}$ by a fixed twist
and shift of degree, which bounds $\dim V_\tau$ above and below by section spaces, with the case $D
= 0$ treated separately, after which 3 gives the limit.

## Depends on

- [Nef and big line bundles](nef-and-big-line-bundles.md)

## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Lemma 5.7 and Lemma 5.8 with its proof, pp. 46–47.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Lemma 2.1, p. 10.
- D. S. Keeler, "Ample filters of invertible sheaves", arXiv:math/0108068 (version 5): Theorem 1.5,
  p. 3 (with the erratum E2.5); Definition 2.9 and Propositions 2.10 and 2.13, pp. 5–6.
- C. Birkar, "The augmented base locus of real divisors over arbitrary fields", arXiv:1312.0239
  (version 1): Theorem 1.5, p. 3; §§2.5–2.6; Lemmas 4.1–4.2 and Proposition 4.3, pp. 7–10.
- The Stacks Project, <https://stacks.math.columbia.edu>: Tags 0BEM, 0BEN, 0BEP (numerical
  polynomials and intersection numbers of coherent sheaves), 0BER (multilinearity) and 0BEV
  (positivity for ample line bundles).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1–3 in this form as `GlobalTheory.Published.NefNumerics` (the conjunction of
  `NefProductNonneg`, `NefBigIff` and `NefRiemannRoch`; only the second assumes $X$ integral), and 4
  as `GlobalTheory.CompanionTheory.Ar.Pub.NefRR`, with the spans of `chartLatNm`; no published
  source stating 4 has been identified.

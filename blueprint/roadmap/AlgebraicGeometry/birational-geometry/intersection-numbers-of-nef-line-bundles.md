# Intersection numbers and Riemann–Roch for nef line bundles

This node is still to be broken down: the statements are precise, but their proofs are not. Let $X$ be
a projective scheme of dimension $n$ over an algebraically closed field $k$ of arbitrary characteristic.

1. (Kleiman.) If $L_1, \dots, L_n$ are nef line bundles on $X$, then $(L_1 \cdots L_n) \ge 0$.
2. If $X$ is integral and $L$ is nef, then $L$ is big if and only if $(L^n) > 0$.
3. If $L$ is nef, then $h^0(X, L^{\otimes m}) = \frac{(L^n)}{n!} m^n + O(m^{n-1})$ as $m \to \infty$.

Over an algebraically closed field of characteristic zero and for smooth $X$, item 2 is Esnault and
Viehweg's Lemma 5.8 a), and for compact Kähler manifolds the analytic form of 2 and 3 is stated with
the [volume of a line bundle](volume-of-a-line-bundle.md).

A good expansion has pages for: Kleiman's theorem on the nonnegativity of intersection numbers of nef
line bundles; the bounds $h^i(X, \mathcal{F} \otimes L^{\otimes m}) = O(m^{n-i})$ for nef $L$ and a
coherent sheaf $\mathcal{F}$, proved by induction on the dimension through hyperplane sections (in
characteristic zero as in Esnault–Viehweg's proof of Lemma 5.8 b), with the
[Kodaira vanishing theorem](kodaira-vanishing-theorem.md); in arbitrary characteristic by Fujita's
vanishing theorem); and the polynomiality of $\chi(X, L^{\otimes m})$ with leading coefficient
$(L^n)/n!$, among the [standard results of coherent cohomology](standard-results-of-coherent-cohomology.md).

## Depends on

- [Nef and big line bundles](nef-and-big-line-bundles.md)

## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Lemma 5.7 and Lemma 5.8 with its proof, pp. 46–47.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Lemma 2.1, p. 10.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 1–3 in this form as `GlobalTheory.Published.NefNumerics`
  (the conjunction of `NefProductNonneg`, `NefBigIff` and `NefRiemannRoch`), and a related form of 3 for
  the lattices of homogeneous elements of a coordinate ring, for line bundles nef on the generic fibre
  of an arithmetic variety, as `GlobalTheory.CompanionTheory.Ar.Pub.NefRR`.

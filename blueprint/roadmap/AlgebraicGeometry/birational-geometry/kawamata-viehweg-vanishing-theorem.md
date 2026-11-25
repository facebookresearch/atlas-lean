# Kawamata–Viehweg vanishing theorem

Let $X$ be an integral smooth projective variety of dimension $n$ over a field of characteristic
zero, $L$ an integral divisor and $D$ an effective $\mathbb{Q}$-divisor on $X$ such that $L - D$ is
[nef and big](nef-and-big-line-bundles.md) and $D$ has
[simple normal crossing support](simple-normal-crossing-divisor.md). Then

$$H^i\bigl(X, \mathcal{O}_X(K_X + L - \lfloor D \rfloor)\bigr) = 0 \qquad (i > 0).$$

For $D = 0$ this says that $H^i(X, \mathcal{O}_X(K_X + L)) = 0$ for $i > 0$ when $L$ is nef and big,
and for $L$ ample it is the [Kodaira vanishing theorem](kodaira-vanishing-theorem.md). The
positivity hypothesis is made on the $\mathbb{Q}$-divisor $L - D$, while the vanishing holds for the
integral divisor $K_X + L - \lfloor D \rfloor$ (Lazarsfeld, after Theorem 2.2).

Esnault and Viehweg prove the theorem over any field $k$ of characteristic zero in the following
form (Corollary 5.12 c)): let $\mathcal{L}$ be an invertible sheaf on $X$, $N \ge 1$ an integer and
$\Delta = \sum_j \alpha_j \Delta_j$ a divisor with snc support whose coefficients satisfy $0 <
\alpha_j < N$; if $\mathcal{L}^N(-\Delta)$ is nef and $c_1(\mathcal{L}^N(-\Delta))^n > 0$, then
$H^b(X, \mathcal{L}^{-1}) = 0$ for $b < n$. For $L$ and $D$ as above, take $\mathcal{L} =
\mathcal{O}_X(L - \lfloor D \rfloor)$ and $\Delta = N(D - \lfloor D \rfloor)$ with $N$ such that
$\Delta$ is integral; its components are the components of $D$ with non-integral coefficient. Then
$\mathcal{L}^N(-\Delta) = \mathcal{O}_X(N(L - D))$ is nef, and its top self-intersection is positive
because $L - D$ is big, by the
[numerical criterion for nef line bundles](volume-of-a-line-bundle.md) applied to this bundle (not
to $\mathcal{L}$); Serre duality turns the conclusion into the vanishing above. Over a field $k$
that is not algebraically closed, $X_{\bar k}$ need not be integral ($\mathbb{P}^1$ over
$\mathbb{Q}(i)$, integral over $\mathbb{Q}$, becomes two copies of
$\mathbb{P}^1_{\bar{\mathbb{Q}}}$), but it is the disjoint union of its connected components, which
are integral, smooth and projective. On each of them the pull-back of $N(L - D)$ is nef, and big: a
decomposition of a multiple of $N(L - D)$ as an ample plus an effective Cartier divisor (Kodaira's
lemma, item 10 of the [standard results](standard-results-of-coherent-cohomology.md)) restricts to
one there. The criterion applied on each component gives a positive top self-intersection, and these
add up to that of $\mathcal{L}^N(-\Delta)$, which extension of scalars does not change.

Esnault and Viehweg also state that $H^b(X, \mathcal{L}^{-1}) = 0$ for $b < \kappa(\mathcal{L})$
when $\mathcal{L}^N(-\Delta)$ is nef (Corollary 5.12 d)). Under the extra hypothesis of c),
$\kappa(\mathcal{L}^N(-\Delta)) = n$ by Lemma 5.8 a), and $\kappa(\mathcal{L}) =
\kappa(\mathcal{L}^N) \ge \kappa(\mathcal{L}^N(-\Delta))$ as $\Delta$ is effective, so
$\kappa(\mathcal{L}) = n$ and c) is the corresponding case of d). The two Iitaka dimensions differ
in general: on $\mathbb{P}^1$, with $\mathcal{L} = \mathcal{O}(1)$, $N = 2$ and $\Delta = [0] +
[\infty]$, $\mathcal{L}^N(-\Delta)$ is trivial, of Iitaka dimension $0$, while $\kappa(\mathcal{L})
= 1$. Their proof (pp. 51–52) reduces c) to the case $\kappa(\mathcal{L}) = n$ of d) and proves that
case; d) in general then follows by induction on $\dim X$, restricting to a general hyperplane
section $H$, for which $\kappa(\mathcal{L}|_H) \ge \kappa(\mathcal{L})$ (the Iitaka dimension need
not drop: the trivial bundle on $\mathbb{P}^2$ restricted to a line keeps $\kappa = 0$). In the case
$\kappa(\mathcal{L}) = n$ they choose an effective divisor $C$ and $\mu \ge 1$ with
$\mathcal{L}^\mu(-C)$ ample (Properties 5.4 d)), so that $\mathcal{L}^{N\nu + \mu}(-\nu\Delta - C)$
is ample for every $\nu$ (Lemma 5.7) and Serre vanishing applies to it; they blow up $X$ so that
$\Delta + C$ becomes a normal crossing divisor (Claim 5.13 shows that the cohomology of
$\mathcal{L}^{-1}$ does not change, although the condition $0 < \alpha_j < N$ is not preserved by
blowing up), replace $N$ and $\Delta$ by $N\nu + \mu$ and $\nu\Delta + C$ for large $\nu$, and
conclude with Corollary 5.12 a). That statement is not reduced to Theorem 5.1 a), their vanishing
theorem for restriction maps derived from the $E_1$-degeneration of the logarithmic de Rham
complexes of cyclic covers, by a blow-up alone: they write $\mathcal{L}^{\nu N}(-\nu\Delta) =
\mathcal{O}_X(B + B')$, make $\Delta + B + B'$ a normal crossing divisor, add the zero set $H$ of a
general section of a globally generated power $(\mathcal{L}^N(-\Delta))^\mu$, so that
$\mathcal{L}^{(\nu + \mu)N} = \mathcal{O}_X(H + (\nu + \mu)\Delta + B + B')$ with all multiplicities
smaller than $(\nu + \mu)N$ for large $\mu$, and only then apply Theorem 5.1 a) with $N' = (\nu +
\mu)N$ (pp. 51–52). The proof of Claim 5.13 uses that the cyclic covers involved have rational
singularities, which is shown with desingularizations of them.

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for $\mathbb{Q}$-divisors, their
  round-down and snc support
- [Nef and big line bundles](nef-and-big-line-bundles.md), for nef and big $\mathbb{Q}$-divisors
- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying variety over a field, which the statement takes smooth, projective and integral

## Proof depends on

- [Logarithmic de Rham complexes and E₁-degeneration](logarithmic-de-rham-complexes-and-e1-degeneration.md),
  for Theorem 5.1 a) and Claim 5.13 of Esnault–Viehweg
- [Principalization of ideal sheaves in characteristic zero](resolution-of-singularities/principalization-of-ideal-sheaves.md), for
  the blow-ups that make the divisors of the proof normal crossing divisors
- [Resolution of singularities of quasi-projective varieties](resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md),
  for the desingularizations of the cyclic covers in the proof of Claim 5.13
- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for Serre vanishing and duality, flat base change, Bertini's theorem for the general member $H$,
  Seshadri's criterion (Lemma 5.7) and Kodaira's lemma (Properties 5.4 d))
- [Volume of a line bundle](volume-of-a-line-bundle.md), for the criterion that a nef invertible sheaf
  $\mathcal{L}$ has $\kappa(\mathcal{L}) = n$ if and only if $c_1(\mathcal{L})^n > 0$ (Esnault–Viehweg,
  Lemma 5.8 a))

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Theorem 2.2 and the remarks after it, pp. 10–11. See also R.
  Lazarsfeld, *Positivity in Algebraic Geometry I, II*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 48, 49, Springer, 2004: the chapter "Vanishing Theorems" (volume I, pp. 239–267); the
  short course refers to its §4.3.A and §9.1.C for a proof by covering constructions.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Corollary 5.12 c) and d), pp. 48–49, with its proof, pp.
  51–52 (induction on $\dim X$); Claim 5.13 and its proof, pp. 49–51; Properties 5.4 d), p. 44;
  Lemma 5.8 a), p. 47; Theorem 5.1, pp. 42–43.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses this result in a specialised form, the case $D = 0$ of a nef and big line bundle over an
  algebraically closed field, as `GlobalTheory.Published.KawamataViehweg`.

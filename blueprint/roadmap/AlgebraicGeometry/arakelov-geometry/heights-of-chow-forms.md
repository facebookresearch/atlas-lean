# Heights of Chow forms

This node is still to be broken down: the identity below is precise, but the constructions it uses
are not.

Let $K$ be a number field, $S = \operatorname{Spec} \mathcal{O}_K$, $\bar E$ a hermitian vector
bundle of rank $N + 1$ over $S$, $\mathbb{P} = \mathbb{P}(\bar E)$ with the quotient metric on
$\mathcal{O}(1)$, and $Z$ an effective cycle on $\mathbb{P}$ of absolute dimension $r + 1$, flat
over $S$. Its Chow divisor $\mathrm{Ch}(Z)$ in $(\mathbb{P}^\vee)^{r+1}$ is the flat closure over
$S$ of the divisor of the classical Chow form of $Z_K$, a multihomogeneous form of multidegree
$(\deg_K Z, \dots, \deg_K Z)$, not the divisor of an arbitrary scalar multiple of an integral model
of that form; its height includes the finite terms $-\sum_\mathfrak{p} n_\mathfrak{p} \log
\mathrm{N}\mathfrak{p}$ of the vertical multiplicities $n_\mathfrak{p}$, which make it independent
of the choice of the form up to scalars (pp. 974–976, 983–984; §1.4.3, pp. 923–924). Bost, Gillet
and Soulé prove (Theorem 4.3.8, case $d_0 = \dots = d_r = 1$)
$$h_0(\mathrm{Ch}(Z)) = h_{\overline{\mathcal{O}(1)}}(Z) - \frac{1}{2} (r + 1) \Bigl( 1 + \frac12 +
\dots + \frac1N \Bigr) [K : \mathbb{Q}] \deg_K(Z),$$
where $h_{\overline{\mathcal{O}(1)}}(Z)$ is the (unnormalized) height of $Z$ and $h_0$ is the height
of the Chow divisor whose archimedean contributions are the means of $\log$ of the absolute value of
the Chow form over products of unit spheres. For the height $h_{\mathrm{Herm}}$ defined with the
hermitian norms on the spaces of multihomogeneous forms instead, $h_{\mathrm{Herm}}(\mathrm{Ch}(Z))
= h_{\overline{\mathcal{O}(1)}}(Z) + [K : \mathbb{Q}] \deg_K(Z)\, \varepsilon(Z)$ with
$|\varepsilon(Z)| \le \frac12 (r + 1) \log(N + 1)$. For generalized Chow forms of multidegree $(d_0,
\dots, d_r)$ Bost, Gillet and Soulé prove analogous identities with different factors: the
coefficient of $h_{\overline{\mathcal{O}(1)}}(Z)$ becomes $\prod_i d_i$, the subtracted term
$\frac12 (\prod_i d_i) \sum_i H_{N_i} / d_i \, [K : \mathbb{Q}] \deg_K(Z)$, with $N_i = \binom{N +
d_i}{d_i} - 1$ and $H_m = 1 + \frac12 + \dots + \frac1m$, and $\log(N_i + 1)$ appears in the
corresponding bound for $\varepsilon$; the displayed correction cannot be used unchanged.

A good expansion has pages for:

- Chow forms: for a field $k$ of characteristic zero and a geometrically prime homogeneous ideal $I$
  of $k[x_0, \dots, x_N]$ with $\dim k[x]/I = r + 1$, the existence of a Chow form of $I$, of
  multidegree given by the degree of $V(I)$, and its uniqueness up to a nonzero scalar (the
  classical theory of Chow and van der Waerden, recalled by Bost, Gillet and Soulé, 4.3.1, Lemma
  4.3.1 and its proof);
- the heights $h_0$ and $h_{\mathrm{Herm}}$ of multihomogeneous forms and of divisors in products of
  projective spaces (Bost–Gillet–Soulé §§1.4 and 4.3.3), their comparison with the Mahler measure of
  the
  [multivariable Mahler measure](../../NumberTheory/heights-mahler-measure/multivariable-mahler-measure/README.md)
  chapter, and the identity above and its bound (Bost–Gillet–Soulé Theorem 4.3.2, 4.3.4, Theorem
  4.3.8; Bost, §1.3, Proposition 1.3);
- Chow forms of prime ideals that are not geometrically prime: an integral variety over a field that
  is not algebraically closed need not be geometrically integral (a quadratic closed point of
  $\mathbb{P}^1$ is cut out by the norm of a linear form), and the integral variant of the existence
  and uniqueness of Chow forms is a separate statement (Bost–Gillet–Soulé, §4.3.2 (ii), p. 976, for
  the incidence characterization over fields of characteristic zero);
- the compatibility of Chow forms with hyperplane sections: fixing the first block of variables
  specializes the Chow form, up to a scalar, to the product of the Chow forms of the components of a
  proper hyperplane section, raised to their multiplicities;
- the upper bound for the arithmetic self-intersection of a model of the image of a projective
  variety under a map given by small sections, in terms of the degree and the height of the image,
  which combines these identities with the [projection formula for heights](height-of-a-cycle.md);
  no single source states it in this form. The form used by Alpöge's library, a checkable target, is
  $a \le [K : \mathbb{Q}] (D + 1) \deg(\text{image}) (h(\text{image}) + t)$ for the model whose
  metric is shifted by $t$, assuming a model of positive image degree, a hermitian spanning lattice
  and generation of the ratios of the function field, with the finite Gauss norms, the mean over
  products of spheres and the positive harmonic correction in the height of the image, and $[K :
  \mathbb{Q}]$ counted once.

## Depends on

- [Height of a cycle](height-of-a-cycle.md)

## Sources

- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027, archived publisher scan
  <https://web.archive.org/web/20170815232351id_/https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/S0894-0347-1994-1260106-X.pdf>:
  §4.3 (generalized Chow divisors 4.3.1–4.3.2 and Lemma 4.3.1, pp. 973–975; heights of Chow divisors
  and forms 4.3.3–4.3.4), Theorem 4.3.8 with (4.3.28)–(4.3.30) and its proof, pp. 989–990.
- J.-B. Bost, "Semi-stability and heights of cycles", Invent. Math. 118 (1994), 223–253,
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0118/LOG_0016.pdf>: §0.1, p. 224, and
  §1.3, Proposition 1.3 with (1.11)–(1.13), pp. 235–236.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses a related identity, for integral closed subschemes of projective space over $\mathcal{O}_K$
  with Fubini–Study metrics defined by frames, as `GlobalTheory.Published.FubiniStudyChowHeight`,
  the existence and uniqueness of Chow forms as `GlobalTheory.Published.ChowFormExists`, and further
  uses the integral variant `chowFormIntExists_holds` (with `IsChowFormInt`), the hyperplane-section
  compatibility `chow_form_hyperplane_section` and the comparison bound of
  `ChowFormHeightComparison`, none of which is stated in this form in a published source.

# Heights of Chow forms

This node is still to be broken down: the identity below is precise, but the constructions it uses are
not.

Let $K$ be a number field, $S = \operatorname{Spec} \mathcal{O}_K$, $\bar E$ a hermitian vector
bundle of rank $N + 1$ over $S$, $\mathbb{P} = \mathbb{P}(\bar E)$ with the quotient metric on
$\mathcal{O}(1)$, and $Z$ an effective cycle on $\mathbb{P}$ of absolute dimension $r + 1$, flat over
$S$. Its Chow divisor $\mathrm{Ch}(Z)$ in $(\mathbb{P}^\vee)^{r+1}$ is defined by the classical Chow form
of $Z_K$, a multihomogeneous form of multidegree $(\deg_K Z, \dots, \deg_K Z)$. Bost, Gillet and Soulé
prove (Theorem 4.3.8, case $d_0 = \dots = d_r = 1$)
$$h_0(\mathrm{Ch}(Z)) = h_{\overline{\mathcal{O}(1)}}(Z) - \frac{1}{2} (r + 1) \Bigl( 1 + \frac12 +
\dots + \frac1N \Bigr) [K : \mathbb{Q}] \deg_K(Z),$$
where $h_{\overline{\mathcal{O}(1)}}(Z)$ is the (unnormalized) height of $Z$ and $h_0$ is the height
of the Chow divisor whose archimedean contributions are the means of $\log$ of the absolute value of
the Chow form over products of unit spheres. For the height $h_{\mathrm{Herm}}$ defined with the
hermitian norms on the spaces of multihomogeneous forms instead,
$h_{\mathrm{Herm}}(\mathrm{Ch}(Z)) = h_{\overline{\mathcal{O}(1)}}(Z) + [K : \mathbb{Q}] \deg_K(Z)\,
\varepsilon(Z)$ with $|\varepsilon(Z)| \le \frac12 (r + 1) \log(N + 1)$. Bost, Gillet and Soulé prove
the same for generalized Chow forms of any multidegree.

A good expansion has pages for:

- Chow forms: for a field $k$ of characteristic zero and a geometrically prime homogeneous ideal $I$ of
  $k[x_0, \dots, x_N]$ with $\dim k[x]/I = r + 1$, the existence of a Chow form of $I$, of multidegree
  given by the degree of $V(I)$, and its uniqueness up to a nonzero scalar (the classical theory of
  Chow and van der Waerden, recalled by Bost, Gillet and Soulé, 4.3.1, Lemma 4.3.1 and its proof);
- the heights $h_0$ and $h_{\mathrm{Herm}}$ of multihomogeneous forms and of divisors in products of
  projective spaces (Bost–Gillet–Soulé §§1.4 and 4.3.3), their comparison with the Mahler measure of
  the [multivariable Mahler measure](../../NumberTheory/heights-mahler-measure/multivariable-mahler-measure/README.md)
  chapter, and the identity above and its bound (Bost–Gillet–Soulé Theorem 4.3.2, 4.3.4,
  Theorem 4.3.8; Bost, §1.3, Proposition 1.3);
- the upper bound for the arithmetic self-intersection of a model of the image of a projective variety
  under a map given by small sections, in terms of the degree and the height of the image, which
  combines these identities with the [projection formula for heights](height-of-a-cycle.md); no single
  source states it in this form.

## Depends on

- [Height of a cycle](height-of-a-cycle.md)

## Sources

- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms",
  J. Amer. Math. Soc. 7 (1994), 903–1027, archived publisher scan
  <https://web.archive.org/web/20170815232351id_/https://www.ams.org/journals/jams/1994-07-04/S0894-0347-1994-1260106-X/S0894-0347-1994-1260106-X.pdf>:
  §4.3 (generalized Chow divisors 4.3.1–4.3.2 and Lemma 4.3.1, pp. 973–975; heights of Chow divisors
  and forms 4.3.3–4.3.4), Theorem 4.3.8 with (4.3.28)–(4.3.30) and its proof, pp. 989–990.
- J.-B. Bost, "Semi-stability and heights of cycles", Invent. Math. 118 (1994), 223–253,
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0118/LOG_0016.pdf>: §0.1, p. 224, and
  §1.3, Proposition 1.3 with (1.11)–(1.13), pp. 235–236.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses a related identity, for integral closed subschemes of
  projective space over $\mathcal{O}_K$ with Fubini–Study metrics defined by frames, as
  `GlobalTheory.Published.FubiniStudyChowHeight`, and the existence and uniqueness of Chow forms as
  `GlobalTheory.Published.ChowFormExists`.

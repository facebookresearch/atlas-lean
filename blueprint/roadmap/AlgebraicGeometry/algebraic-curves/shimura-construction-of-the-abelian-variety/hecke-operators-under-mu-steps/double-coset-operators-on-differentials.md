# Double coset operators on weight-two cusp forms as maps of differentials

Let $N$ be a positive integer, $\Gamma$ a group of level $N$, $X = \mathfrak{H}^*/\Gamma$ the compact Riemann surface of
the [modular curve page](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
and $f \mapsto \omega_f$ the isomorphism of $S_2(\Gamma)$ onto the holomorphic differentials $\Omega^1(X)$ of
[weight-two cusp forms as holomorphic differentials](../cusp-forms-as-one-forms-steps/weight-two-cusp-forms-as-holomorphic-differentials.md).
Let $\alpha \in \mathrm{GL}_2(\mathbb{Q})$ with $\det \alpha > 0$, let $\Gamma_\alpha = \Gamma \cap \alpha^{-1} \Gamma \alpha$,
$X_\alpha = \mathfrak{H}^*/\Gamma_\alpha$, and let $\pi_1, \pi_2 \colon X_\alpha \to X$ be the holomorphic maps induced by
$z \mapsto z$ and $z \mapsto \alpha z$, as on the
[Hecke endomorphisms page](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md).
Write $\pi_2^* \colon \Omega^1(X) \to \Omega^1(X_\alpha)$ for the pullback of differentials and
$\mathrm{Tr}_{\pi_1} \colon \Omega^1(X_\alpha) \to \Omega^1(X)$ for the trace along $\pi_1$: if
$\Gamma = \bigsqcup_i \Gamma_\alpha \beta_i$ and $\eta \in \Omega^1(X_\alpha)$ pulls back to $\mathfrak{H}$ as $h(z)\,dz$, then
$\mathrm{Tr}_{\pi_1} \eta$ is the holomorphic differential on $X$ whose pullback to $\mathfrak{H}$ is
$\sum_i h(\beta_i z)\, d(\beta_i z)$. Then, for the operator $[\Gamma \alpha \Gamma]_2$ of the
[Hecke operators page](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md),

$$\omega_{f \mid [\Gamma \alpha \Gamma]_2} = \mathrm{Tr}_{\pi_1}\bigl(\pi_2^* \omega_f\bigr) \qquad (f \in S_2(\Gamma)).$$

On $\mathfrak{H}$ this is the identity

$$(f \mid [\Gamma \alpha \Gamma]_2)(z)\, dz = \sum_i f(\alpha \beta_i z)\, d(\alpha \beta_i z),$$

where $\Gamma \alpha \Gamma = \bigsqcup_i \Gamma \alpha \beta_i$.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
  for the compact Riemann surfaces $\mathfrak{H}^*/\Gamma$ and $\mathfrak{H}^*/\Gamma_\alpha$
- [Weight-two cusp forms as holomorphic differentials on $\mathfrak{H}^*/\Gamma$](../cusp-forms-as-one-forms-steps/weight-two-cusp-forms-as-holomorphic-differentials.md),
  for $\omega_f$
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md),
  for $[\Gamma \alpha \Gamma]_2$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md),
  for $\Gamma_\alpha$, $\pi_1$ and $\pi_2$

## Proof depends on

- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md),
  for $f \mid [\Gamma \alpha \Gamma]_2 = \sum_\nu f \mid_2 \alpha_\nu$ over any decomposition
  $\Gamma \alpha \Gamma = \bigsqcup_\nu \Gamma \alpha_\nu$
- [Weight-two cusp forms as holomorphic differentials on $\mathfrak{H}^*/\Gamma$](../cusp-forms-as-one-forms-steps/weight-two-cusp-forms-as-holomorphic-differentials.md),
  for the injectivity of $f \mapsto \omega_f$ and of the pullback to $\mathfrak{H}$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the decomposition $\Gamma \alpha \Gamma = \bigsqcup_i \Gamma \alpha \beta_i$ for $\Gamma = \bigsqcup_i \Gamma_\alpha \beta_i$
  (Milne's course notes, Lemma 5.30);
- the identity $(f \mid_2 \beta)(z)\, dz = f(\beta z)\, d(\beta z)$ for $\beta \in \mathrm{GL}_2(\mathbb{Q})$ with
  $\det \beta > 0$, from $d(\beta z) = \det(\beta)\,(c z + d)^{-2}\, dz$ and the weight-two normalization
  $(f \mid [\beta]_2)(z) = \det(\beta)\,(c z + d)^{-2} f(\beta z)$ of Shimura (1973), p. 527;
- the computation of $\mathrm{Tr}_{\pi_1}(\pi_2^* \omega_f)$ on $\mathfrak{H}$: $\pi_2^* \omega_f$ pulls back to
  $f(\alpha z)\, d(\alpha z)$, and the trace sums its pullbacks along the $\beta_i$;
- that $\mathrm{Tr}_{\pi_1}$ is well defined, independent of the $\beta_i$ and holomorphic, including at the branch
  points of $\pi_1$, the elliptic points and the cusps.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the correspondence
  $X(\Gamma' \alpha \Gamma)$, "the locus of $z \times \alpha(z)$ modulo $\Gamma \times \Gamma'$", and (1.3)); §2, p. 527 (the
  definition $(f \mid [\alpha]_k)(z) = \det(\alpha)^{k/2} (c z + d)^{-k} f(\alpha(z))$).
- J. S. Milne, *Modular Functions and Modular Forms*, course notes, version 1.31 (2017),
  <https://www.jmilne.org/math/CourseNotes/MF.pdf>: Lemma 5.30, p. 81 (if $\Gamma = \bigcup (\Gamma \cap \alpha^{-1} \Gamma \alpha) \beta_i$
  is a disjoint union, then so is $\Gamma \alpha \Gamma = \bigcup \Gamma \alpha_i$ with $\alpha_i = \alpha \beta_i$), and the
  paragraph after it, p. 81 (a modular form regarded as a $k$-fold differential, with $T(p)$ "the pull-back followed by
  the trace"); Remark 4.8, p. 50 (the computation $d(\gamma z) = (c z + d)^{-2}\, dz$ for $\gamma \in \mathrm{SL}_2(\mathbb{Z})$).
- W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics 79, American Mathematical
  Society, 2007; author's version <https://wstein.org/books/modform/stein-modform.pdf>, page numbers of that version:
  §3.1, p. 37 (for $\Gamma_0(N)$ and $n$ prime to $N$, the Hecke operator $T_n$ as $\pi_{1*} \circ \pi_2^*$ on
  differentials, for two maps $X_0(nN) \to X_0(N)$).

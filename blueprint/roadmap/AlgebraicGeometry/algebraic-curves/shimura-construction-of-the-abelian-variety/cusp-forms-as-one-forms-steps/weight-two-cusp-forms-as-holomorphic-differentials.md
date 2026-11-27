# Weight-two cusp forms as holomorphic differentials on $\mathfrak{H}^*/\Gamma$

Let $N$ be a positive integer, $\Gamma$ a group of level $N$, that is,
$\Gamma_1(N) \subset \Gamma \subset \Gamma_0(N)$, let $X = \mathfrak{H}^*/\Gamma$ be the compact Riemann surface of the
[modular curve page](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
$p \colon \mathfrak{H} \to X$ the restriction of the quotient map, and $\Omega^1(X)$ the complex vector space of
holomorphic differentials on $X$. Let $S_2(\Gamma)$ be the space of weight-two
[cusp forms](../../../../NumberTheory/modular-forms-q-series/modular-forms/cusp-form.md) for $\Gamma$.

For every $f \in S_2(\Gamma)$ there is a unique holomorphic differential $\omega_f$ on $X$ with

$$p^* \omega_f = f(z)\, dz,$$

$z$ the standard coordinate on $\mathfrak{H}$, and $f \mapsto \omega_f$ is an isomorphism of complex vector spaces
$S_2(\Gamma) \to \Omega^1(X)$.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
  for the compact Riemann surface $\mathfrak{H}^*/\Gamma$
- [Cusp form](../../../../NumberTheory/modular-forms-q-series/modular-forms/cusp-form.md), for $S_2(\Gamma)$
- [Congruence subgroup $\Gamma_0(N)$](../../../../NumberTheory/modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md)
- [Congruence subgroup $\Gamma_1(N)$](../../../../NumberTheory/modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)

## Proof depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
  for the charts of $\mathfrak{H}^*/\Gamma$ at the elliptic points and the cusps
- [Cusp form](../../../../NumberTheory/modular-forms-q-series/modular-forms/cusp-form.md), for the invariance
  $f \mid_2 \gamma = f$, $\gamma \in \Gamma$, and the expansions at the cusps

## Expansion

This node is still to be broken down. A good expansion states and links:

- the invariance of $f(z)\,dz$ under $\Gamma$: for $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma$,
  $d(\gamma z) = (c z + d)^{-2}\, dz$, so $\gamma^*(f(z)\,dz) = (f \mid_2 \gamma)(z)\, dz = f(z)\, dz$ (Milne,
  Remark 4.8), and its descent to a holomorphic differential on the complement in $X$ of the elliptic points and
  the cusps, where $p$ is a local isomorphism;
- the orders at the elliptic points and the cusps, in Milne's Lemma 4.11 for weight two: at the image $P$ of an
  elliptic point $Q$ of order $e$, $\mathrm{ord}_Q(f) = e\, \mathrm{ord}_P(\omega) + e - 1$, and at a cusp,
  $\mathrm{ord}_Q(f) = \mathrm{ord}_P(\omega) + 1$, the order of $f$ being taken in the local parameter at the cusp; so
  $f$ is holomorphic on $\mathfrak{H}$ and vanishes at every cusp if and only if $\omega_f$ is holomorphic on $X$;
- the converse direction: the pullback to $\mathfrak{H}$ of a holomorphic differential on $X$ is $g(z)\,dz$ with
  $g \in S_2(\Gamma)$, which gives surjectivity, and injectivity from $p^*\omega_f = f(z)\,dz$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the isomorphism
  $\mu \colon S_2(\Gamma) \to D_J$ defined by $\delta\psi(\mu(f)) = f(z)\,dz$, which rests on this identification).
- J. S. Milne, *Modular Functions and Modular Forms*, course notes, version 1.31 (2017),
  <https://www.jmilne.org/math/CourseNotes/MF.pdf>: Remark 4.8, pp. 50–51 (a differential $f(z)\,dz$ on $\mathfrak{H}$ is
  invariant under a subgroup of finite index of $\mathrm{SL}_2(\mathbb{Z})$ if and only if $f$ is a meromorphic modular
  form of weight $2$, and the correspondence with meromorphic differentials on the quotient), and Lemma 4.11, p. 52
  (the orders at the elliptic points, the cusps and the remaining points), where Milne writes $M_k(\Gamma)$ for the
  forms of weight $2k$, so weight two is his $k = 1$.
- W. Stein, *Modular Forms: A Computational Approach*, Graduate Studies in Mathematics 79, American Mathematical
  Society, 2007; author's version <https://wstein.org/books/modform/stein-modform.pdf>, page numbers of that version:
  §3.1, p. 36 (for $\Gamma_0(N)$: a cusp form of weight $2$ is a function $f$ on $\mathfrak{H}$ such that $f(z)\,dz$
  defines a holomorphic differential on $X_0(N)$).

# Galois representations attached to weight-one eigenforms

This node is still to be broken down. Let $N \ge 1$ and let $f = \sum_{n \ge 1} a_n(f) q^n \in S_1(\Gamma_1(N))$,
$q = e^{2\pi i \tau}$, be a normalized eigenform with nebentypus $\chi$: a
[cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md) of weight $1$ for
[$\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md) with $a_1(f) = 1$ that is an
eigenvector of every Hecke operator $T_n$ and every diamond operator $\langle d \rangle$
(Hecke eigenforms and newforms for Γ₁(N)),
with $f \mid_1 \gamma = \chi(d) f$ for every
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$ in
[$\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md). Let
$K_f = \mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$, a number field, let $\ell$ be a prime, $\lambda$ a maximal ideal of
$\mathcal{O}_{K_f}$ over $\ell$ and $K_{f,\lambda}$ the completion of $K_f$ at $\lambda$, and let $\overline{\mathbb{Z}}$ be the
integral closure of $\mathbb{Z}$ in $\overline{\mathbb{Q}}$. Then there is an irreducible continuous representation

$$\rho_{f,\lambda} \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(K_{f,\lambda}),$$

for the Krull topology, such that for every prime $p \nmid \ell N$ and every maximal ideal $\mathfrak{p}$ of
$\overline{\mathbb{Z}}$ over $p$ the inertia group of $\mathfrak{p}$ acts trivially and every arithmetic Frobenius element
$\sigma$ at $\mathfrak{p}$ ($\sigma(x) \equiv x^p \pmod{\mathfrak{p}}$ for all $x \in \overline{\mathbb{Z}}$) has

$$\det\bigl(X - \rho_{f,\lambda}(\sigma)\bigr) = X^2 - a_p(f)\,X + \chi(p).$$

Irreducible means that no line of $K_{f,\lambda}^2$ is stable under every $\rho_{f,\lambda}(\sigma)$. This is the case
$k = 1$ of
[Galois representations attached to normalized eigenforms](../../../not-yet-classified/exists-galois-rep-charpoly-frob.md).
Deligne and Serre's Théorème 4.1,
[Galois representations attached to weight-one eigenforms (Deligne–Serre)](../../../not-yet-classified/exists-galois-rep-trace-det-frob-of-weig.md),
gives a representation into $\mathrm{GL}_2(\mathbb{C})$ with finite image; the representation above is a form of it over
$K_f$, extended to $K_{f,\lambda}$.

## Depends on

- [Cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md), for $S_1(\Gamma_1(N))$
- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the nebentypus

## Proof depends on

- [Galois representations attached to weight-one eigenforms (Deligne–Serre)](../../../not-yet-classified/exists-galois-rep-trace-det-frob-of-weig.md), Deligne–Serre's Théorème 4.1, for a representation $\rho \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{C})$ with finite image, unramified outside $N$, with $\operatorname{Tr} \rho(\sigma) = a_p(f)$ and $\det \rho(\sigma) = \chi(p)$ for every arithmetic Frobenius element $\sigma$ at a prime $p \nmid N$, and irreducible because $f$ is a cusp form
- [Modular forms of type (k, ε) on Γ₀(N)](../deligne-serre-theorem-on-weight-one-forms/modular-forms-of-type-k-epsilon.md), for the hypotheses of Théorème 4.1: $f$ is a nonzero modular form of type $(1, \chi)$, as $\chi(-1) = -1$ (the transformation law at $-1 \in \Gamma_0(N)$ gives $f = -\chi(-1) f$), and an eigenvector of each $T_p$, $p \nmid N$, whose eigenvalue is the coefficient $a_p(f)$ of $q$ in $f | T_p$, as $a_1(f) = 1$
- [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), for the realizability over $K_f$: each element of the finite group $\rho(\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}))$ is conjugate to $\rho(\sigma)$ for an arithmetic Frobenius element $\sigma$ at some prime $p \nmid N$ (as in Deligne–Serre, §6.12), so that the character of $\rho$ takes its values in $K_f$, and $\det \rho$ is $\chi$ as a character of the Galois group (Remarque 4.4)
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $\chi$ as a character of the Galois group through its action on the $N$-th roots of unity, on which an arithmetic Frobenius element at $p \nmid N$ acts by $\zeta \mapsto \zeta^p$ and a complex conjugation $c$ by inversion: $\det \rho(c) = \chi(-1) = -1$, so $\rho(c)$, of order $2$, has the distinct rational eigenvalues $1$ and $-1$ (Remarques 4.4 and 4.5)

## Expansion

This node is still to be broken down. A good expansion states and links:

- Deligne–Serre's Théorème 4.1 and its proof,
  [The Deligne–Serre theorem on modular forms of weight one](../deligne-serre-theorem-on-weight-one-forms/README.md);
- the realizability of $\rho$ over $K_f$ (Deligne–Serre, footnote (2), p. 521): the image of $\rho$ contains $\rho(c)$,
  whose eigenvalues $1$ and $-1$ are rational and distinct, so the Schur index of $\rho$ is $1$ (Schur, IX a, as cited
  there) and $\rho$ is realizable over the field of values of its character, which lies in $K_f$;
- the continuity of a representation with finite image, and the absolute irreducibility that persists after extending
  scalars from $K_f$ to $K_{f,\lambda}$.

## Sources

- P. Deligne and J.-P. Serre, "Formes modulaires de poids 1", Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  <http://www.numdam.org/item/ASENS_1974_4_7_4_507_0>: Théorème 4.1, pp. 513–514 ("Soient $N$ un entier $\geqq 1$,
  $\varepsilon$ un caractère de Dirichlet mod $N$ tel que $\varepsilon(-1) = -1$, et
  $f$ une forme modulaire de type $(1, \varepsilon)$ sur $\Gamma_0(N)$, non identiquement nulle. On suppose que $f$ est
  fonction propre des $T_p$, $p \nmid N$, avec pour valeurs propres $a_p$. Il existe alors une représentation linéaire
  $\rho \colon G \to \mathrm{GL}_2(\mathbf{C})$, où $G = \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$, qui est non ramifiée en dehors
  de $N$ et telle que (4.1.1) $\mathrm{Tr}(F_{\rho,p}) = a_p$ et $\det(F_{\rho,p}) = \varepsilon(p)$ pour tout $p \nmid N$. Cette
  représentation est irréductible si et seulement si $f$ est parabolique"), with $F_{\rho,p}$ the image under $\rho$ of
  Artin's Frobenius substitution, whose inverse is the geometric Frobenius; Remarques 4.4 and 4.5, p. 514
  ($\det(\rho) = \varepsilon$, with $\varepsilon$ identified with a character of $G$ through the action of $G$ on the $N$-th
  roots of unity, and $\rho(c)$ conjugate to $\left(\begin{smallmatrix} 1 & 0 \\ 0 & -1 \end{smallmatrix}\right)$ for the
  complex conjugation $c$, as $\varepsilon$ is odd); Remarque 6.5 and its footnote (2), p. 521 ("Cela résulte du fait que la
  représentation $\rho$ du théorème 4.1 est réalisable sur $K$ : son image contient un élément à valeurs propres
  rationnelles et distinctes (l'élément $\rho(c)$ de 4.5) et cela entraîne que son indice de Schur est 1 (cf. [20], IX a);
  elle est donc réalisable sur le corps des valeurs de son caractère"), with $K$ a finite extension of $\mathbf{Q}$
  containing the $a_p$ and the $\varepsilon(p)$, as in Théorème 6.1, p. 520; §6.12, p. 523, for Chebotarev's theorem
  making each element of a finite image a Frobenius element.
- I. Schur, "Arithmetische Untersuchungen über endliche Gruppen linearer Substitutionen", Sitzungsberichte der
  Preussischen Akademie der Wissenschaften (1906), 164–184: IX a, as cited in Deligne–Serre (1974), footnote (2),
  p. 521; not read.
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section and remark numbers: §12.5, Remark 12.5.9 ("Deligne and Serre [...] construct
  a representation using the representations associated to congruent eigenforms of higher weight"; the image is finite
  and a basis can be chosen with image in $\mathrm{GL}_2(\mathcal{O})$).
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §3.1, Theorem 3.3, pp. 87–88, for a
  newform of weight one.
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer (2005):
  Theorem 9.6.5, p. 393, as cited by the statement of which this is a case; not read.

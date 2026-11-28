# Galois representations attached to eigenforms of weight at least three

This node is still to be broken down. Let $N \ge 1$ and $k \ge 3$, and let
$f = \sum_{n \ge 1} a_n(f) q^n \in S_k(\Gamma_1(N))$, $q = e^{2\pi i \tau}$, be a normalized eigenform with
nebentypus $\chi$: a [cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md) of weight $k$ for
[$\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md) with $a_1(f) = 1$ that is an
eigenvector of every Hecke operator $T_n$ and every diamond operator $\langle d \rangle$
(Hecke eigenforms and newforms for Γ₁(N)),
with $f \mid_k \gamma = \chi(d) f$ for every
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$ in
[$\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md). Let
$K_f = \mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$, a number field, let $\ell$ be a prime, $\lambda$ a maximal ideal of
$\mathcal{O}_{K_f}$ over $\ell$ and $K_{f,\lambda}$ the completion of $K_f$ at $\lambda$, and let $\overline{\mathbb{Z}}$ be the
integral closure of $\mathbb{Z}$ in $\overline{\mathbb{Q}}$. Then there is an irreducible continuous representation

$$\rho_{f,\lambda} \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(K_{f,\lambda}),$$

for the Krull topology, such that for every prime $p \nmid \ell N$ and every maximal ideal $\mathfrak{p}$ of
$\overline{\mathbb{Z}}$ over $p$ the inertia group of $\mathfrak{p}$ acts trivially and every arithmetic Frobenius element
$\sigma$ at $\mathfrak{p}$ ($\sigma(x) \equiv x^p \pmod{\mathfrak{p}}$ for all $x \in \overline{\mathbb{Z}}$) has

$$\det\bigl(X - \rho_{f,\lambda}(\sigma)\bigr) = X^2 - a_p(f)\,X + \chi(p)\,p^{k-1}.$$

Irreducible means that no line of $K_{f,\lambda}^2$ is stable under every $\rho_{f,\lambda}(\sigma)$. This is the case
$k \ge 3$ of
[Galois representations attached to normalized eigenforms](../../../not-yet-classified/exists-galois-rep-charpoly-frob.md).

## Depends on

- [Cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md), for $S_k(\Gamma_1(N))$
- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the nebentypus

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Expansion

This node is still to be broken down. A good expansion states and links:

- Deligne's construction from the $\ell$-adic cohomology of the modular curves with coefficients in the
  $(k-2)$-th symmetric power of the first relative $\ell$-adic cohomology of the universal elliptic curve, with its
  Hecke action (Diamond–Im, Remark 12.5.8; Deligne, §§3–4), and the $\lambda$-part on which the Hecke algebra acts
  through the eigenvalues of $f$;
- the congruence formula $T_p = F + I_p^* V$, $FV = p^{k-1}$ on that cohomology for $p$ prime to the level and to
  $\ell$ (Deligne, Théorème 4.9, in his notation with $k - 2$ in place of $k$), with the unramifiedness at $p \nmid \ell N$
  from the good reduction of the modular curves and the smoothness of the universal elliptic curve there, which give
  the characteristic polynomial;
- the comparison with Kato's representation $V_{F_\lambda}(f)$ of a newform, in the geometric-Frobenius normalization of
  Galois representations attached to newforms and their Hodge filtration at p,
  whose dual has the characteristic polynomials above;
- the reduction from normalized eigenforms to newforms: the representation depends only on the newform associated to
  $f$ (Diamond–Im, Remark 12.5.3), with the newform theory planned on
  Hecke eigenforms and newforms for Γ₁(N);
- irreducibility (Ribet, Theorem 2.3, as cited by Diamond–Im, Remark 12.5.4).

## Sources

- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section, remark and equation numbers: §12.5, (12.5.1), (12.5.2) ("A construction due
  to Shimura [...] for $k = 2$, Deligne [Del1] for $k > 2$, and Deligne and Serre [DeSe] for $k = 1$, attaches to $f$ a
  certain compatible family of $\ell$-adic Galois representations", with characteristic polynomial
  $X^2 - \theta(T_p) X + p\theta(S_p)$, $\theta(S_p) = p^{k-2}\varepsilon(p)$), Remarks 12.5.1, 12.5.3, 12.5.4 and 12.5.8.
- P. Deligne, "Formes modulaires et représentations $\ell$-adiques", Séminaire Bourbaki, exp. 355 (1969),
  Lecture Notes in Math. 179, Springer (1971), 139–172, <http://www.numdam.org/item?id=SB_1968-1969__11__139_0>:
  Théorème 4.1 (Igusa), Proposition 4.8 and Théorème 4.9 (Formule de congruence), pp. 160–167.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §3.1, p. 87 ("The construction of
  $\ell$-adic representations associated to newforms was generalized to weight greater than 1 by Deligne [De] using
  étale cohomology").
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer (2005):
  Theorem 9.6.5, p. 393, as cited by the statement of which this is a case; not read.

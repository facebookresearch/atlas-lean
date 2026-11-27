# Galois representations attached to weight-two eigenforms

This node is still to be broken down. Let $N \ge 1$ and let $f = \sum_{n \ge 1} a_n(f) q^n \in S_2(\Gamma_1(N))$,
$q = e^{2\pi i \tau}$, be a normalized eigenform with nebentypus $\chi$: a
[cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md) of weight $2$ for
[$\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md) with $a_1(f) = 1$ that is an
eigenvector of the [Hecke operators](../../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md) $T_p$
for all primes $p$ and of the diamond operators, with $f \mid_2 \gamma = \chi(d) f$ for every
$\gamma = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$ in
[$\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md). Let
$K_f = \mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$, a number field, let $\ell$ be a prime, $\lambda$ a maximal ideal of
$\mathcal{O}_{K_f}$ over $\ell$ and $K_{f,\lambda}$ the completion of $K_f$ at $\lambda$. Let $\overline{\mathbb{Z}}$ be the
integral closure of $\mathbb{Z}$ in $\overline{\mathbb{Q}}$ and give $G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ its
Krull topology. Then there is a continuous representation

$$\rho_{f,\lambda} \colon G_{\mathbb{Q}} \to \mathrm{GL}_2(K_{f,\lambda})$$

such that for every prime $p \nmid \ell N$ and every maximal ideal $\mathfrak{p}$ of $\overline{\mathbb{Z}}$ over $p$:

- the inertia group of $\mathfrak{p}$, the elements of $G_{\mathbb{Q}}$ that fix $\mathfrak{p}$ and act trivially on
  $\overline{\mathbb{Z}}/\mathfrak{p}$, acts trivially, so $\rho_{f,\lambda}$ is unramified at $p$;
- every $\sigma \in G_{\mathbb{Q}}$ with $\sigma(x) \equiv x^p \pmod{\mathfrak{p}}$ for all $x \in \overline{\mathbb{Z}}$, an arithmetic
  Frobenius element at $\mathfrak{p}$, has

    $$\det\bigl(X - \rho_{f,\lambda}(\sigma)\bigr) = X^2 - a_p(f)\,X + \chi(p)\,p,$$

    with $a_p(f)$ and $\chi(p)$ in $K_f \subset K_{f,\lambda}$.

This is the weight-two case of
[Galois representations attached to normalized eigenforms](../../../not-yet-classified/exists-galois-rep-charpoly-frob.md)
without its irreducibility clause, which is
[Irreducibility of the Galois representations of weight-two eigenforms](irreducibility-of-the-galois-representations-of-weight-two-eigenforms.md).
For $N \le 4$ there is no such $f$, as $S_2(\Gamma_1(N)) = 0$.

## Depends on

- [Cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md), for $S_2(\Gamma_1(N))$
- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Congruence subgroup $\Gamma_0(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma0.md), for the nebentypus
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for the eigenform condition

## Proof depends on

- [Tate module of the abelian variety attached to a weight-two eigenform](tate-module-of-the-abelian-variety-of-a-weight-two-eigenform.md), for $V_\ell(A_f)$, free of rank $2$ over $\mathbb{Q}_\ell \otimes K_f$, with its unramified $G_{\mathbb{Q}}$-action and characteristic polynomials of Frobenius, for $N \ge 5$
- [Base change to a finite completion as a product of completions](../../discriminants-ramification/completions-of-number-fields-at-finite-places/the-finite-place-completion-tensor-product/completion-tensor-product-alg-equiv.md), for $\mathbb{Q}_\ell \otimes_{\mathbb{Q}} K_f \cong \prod_{\lambda \mid \ell} K_{f,\lambda}$, whose factor at $\lambda$ gives $\rho_{f,\lambda}$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the vanishing $S_2(\Gamma_1(N)) = 0$ for $N < 5$, where $X_1(N)$ has genus $0$ (Conrad, p. 59);
- the construction for $N \ge 5$: the factor $V_\ell(A_f) \otimes_{\mathbb{Q}_\ell \otimes K_f} K_{f,\lambda}$ of $V_\ell(A_f)$ under
  $\mathbb{Q}_\ell \otimes K_f \cong \prod_{\lambda \mid \ell} K_{f,\lambda}$, a two-dimensional $K_{f,\lambda}$-vector space with a
  continuous $G_{\mathbb{Q}}$-action whose Frobenius characteristic polynomials are the images of
  $X^2 - (1 \otimes a_p(f)) X + 1 \otimes p\chi(p)$ (Conrad, Corollary 5.15; Diamond–Im, §12.5);
- the passage from one arithmetic Frobenius element at one prime over $p$ to every arithmetic Frobenius element at
  every maximal ideal of $\overline{\mathbb{Z}}$ over $p$: $G_{\mathbb{Q}}$ permutes these maximal ideals transitively, two
  arithmetic Frobenius elements at $\mathfrak{p}$ differ by an element of its inertia group, and characteristic
  polynomials are invariant under conjugation.

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.1, p. 59 ("$S_2(\Gamma_1(N), \mathbf{C}) = 0$ if $N < 5$"); §5.2, Corollary 5.15, p. 69 ("Let
  $f \in S_2(\Gamma_1(N), \mathbf{C})$ be a newform and $\lambda$ a place of $K_f$ over $\ell$. There exists a continuous
  representation $\rho_{f,\lambda} \colon G_{\mathbf{Q}} \to GL(2, K_{f,\lambda})$ unramified at all $p \nmid N\ell$, with
  $\mathrm{Frob}_p$ having characteristic polynomial $X^2 - a_p(f) X + p\chi_f(p) \in K_{f,\lambda}[X]$"), stated there for
  newforms.
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section, remark and equation numbers: §12.5, (12.5.1), (12.5.2) and Remark 12.5.1
  (for $f \in S_k(\Gamma_1(N))$ a normalized eigenform for the Hecke operators in $\mathbf{T}_N$, "A construction due to
  Shimura [...] for $k = 2$ [...] attaches to $f$ a certain compatible family of $\ell$-adic Galois representations",
  continuous, unramified at $p \nmid N\ell$, with characteristic polynomial $X^2 - \theta(T_p) X + p\theta(S_p)$ of an
  arithmetic Frobenius), the construction for $k = 2$ from $W_\ell(J_1(N)) \otimes_{\mathbf{T} \otimes \mathbf{Q}_\ell} K_\lambda$,
  and Remark 12.5.6.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §3.1, pp. 84–86, (3.1.1) and
  Theorem 3.1 (a) ("If $p \nmid N\ell$ then $\rho$ is unramified at $p$ and $\rho(\mathrm{Frob}_p)$ has characteristic
  polynomial $X^2 - a_p X + p\psi(p)$"), for a newform of weight two, with "Part (a) was established by Shimura".
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer (2005):
  Theorem 9.6.5, p. 393, as cited by the statement it specializes; §9.5, p. 386, and §9.6, p. 392, from the table of
  contents. These pages were not read.

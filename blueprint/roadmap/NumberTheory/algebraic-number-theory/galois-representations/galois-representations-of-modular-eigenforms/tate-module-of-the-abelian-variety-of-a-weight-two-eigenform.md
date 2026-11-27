# Tate module of the abelian variety attached to a weight-two eigenform

This node is still to be broken down. Let $N \ge 5$, let $J_{\mathbb{Q}}$ be the Jacobian of $X_1(N)_{\mathbb{Q}}$, the generic
fibre of the Jacobian $J$ of the [modular curve $X_1(N)$ over $\mathbb{Z}[1/N]$](modular-curve-x1-n-over-z-1-over-n.md),
and let the Hecke algebra $\mathbb{T}_1(N)$ act on $J$ through the $(\ )_*$-operators of
[Hecke operators on the Jacobian of X₁(N)](hecke-operators-on-the-jacobian-of-x1-n.md), which induce the
classical $T_p$ and $\langle n \rangle$ on $S_2(\Gamma_1(N))$.

Let $f = \sum_{n \ge 1} a_n(f) q^n \in S_2(\Gamma_1(N))$, $q = e^{2\pi i \tau}$, be a normalized eigenform: a
[cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md) of weight $2$ for
[$\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md) with $a_1(f) = 1$ that
is an eigenvector of the [Hecke operators](../../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md)
$T_p$ for all primes $p$ and of the diamond operators $\langle n \rangle$, $n \in (\mathbb{Z}/N\mathbb{Z})^\times$. Let
$\chi$ be its nebentypus, $\langle n \rangle f = \chi(n) f$, let
$\theta_f \colon \mathbb{T}_1(N) \to \mathbb{C}$ send each $T$ to its eigenvalue on $f$, so $\theta_f((T_p)_*) = a_p(f)$ and
$\theta_f(\langle n \rangle_*) = \chi(n)$, let $K_f = \mathbb{Q}(a_n(f) : n \ge 1) \subset \mathbb{C}$, and let
$\mathfrak{p}_f = \ker \theta_f$. Let

$$A_f = J_{\mathbb{Q}} / \mathfrak{p}_f J_{\mathbb{Q}}$$

be the [quotient](../../../../AlgebraicGeometry/abelian-varieties/quotient-by-an-abelian-subvariety.md) of $J_{\mathbb{Q}}$ by
its abelian subvariety $\mathfrak{p}_f J_{\mathbb{Q}}$, the sum of the images of the elements of $\mathfrak{p}_f$; it is an
abelian variety over $\mathbb{Q}$, and $\mathbb{T}_1(N)$ acts on it through $\mathbb{T}_1(N)/\mathfrak{p}_f$, whence an action of
$K_f$, identified with $(\mathbb{T}_1(N)/\mathfrak{p}_f) \otimes_{\mathbb{Z}} \mathbb{Q}$ by $\theta_f$, on $A_f$ in the isogeny category.
Then, for every prime $\ell$:

1. $\dim A_f = [K_f : \mathbb{Q}]$;
2. $V_\ell(A_f) = \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} \varprojlim_n A_f[\ell^n](\overline{\mathbb{Q}})$ is a free
   $\mathbb{Q}_\ell \otimes_{\mathbb{Q}} K_f$-module of rank $2$, on which $G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acts
   continuously and $\mathbb{Q}_\ell \otimes K_f$-linearly, unramified at every prime $p \nmid N\ell$;
3. for every prime $p \nmid N\ell$ and every arithmetic Frobenius element $\mathrm{Frob}_p$ at a prime over $p$, the
   characteristic polynomial of $\mathrm{Frob}_p$ on $V_\ell(A_f)$ over $\mathbb{Q}_\ell \otimes_{\mathbb{Q}} K_f$ is

    $$X^2 - (1 \otimes a_p(f)) X + 1 \otimes p\,\chi(p).$$

Diamond and Im introduce this quotient with a reference to Shimura's Theorem 1, the subject of
[Shimura's abelian variety attached to a weight-two eigenform](../../../modular-forms-q-series/modular-forms/shimura-abelian-variety-of-an-eigenform.md).

## Depends on

- [Hecke operators on the Jacobian of X₁(N) over Z[1/N]](hecke-operators-on-the-jacobian-of-x1-n.md), for $J_{\mathbb{Q}}$ and the action of $\mathbb{T}_1(N)$
- [Cusp form](../../../modular-forms-q-series/modular-forms/cusp-form.md), for $S_2(\Gamma_1(N))$
- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md)
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for the eigenform condition
- [Quotient of an abelian variety by an abelian subvariety](../../../../AlgebraicGeometry/abelian-varieties/quotient-by-an-abelian-subvariety.md), for $A_f$
- [Abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{Q}$ and their dimension

## Proof depends on

- [Frobenius on the Tate module of J₁(N)](frobenius-on-the-tate-module-of-j1-n.md), for the representation $\rho_{N,\ell}$ on $V_\ell(N)$ and its characteristic polynomials $X^2 - (T_p)_* X + p \langle p \rangle_*$
- [The rational Tate module of J₁(N) is free of rank two over the Hecke algebra](tate-module-of-j1-n-is-free-over-the-hecke-algebra.md), for $V_\ell(N)$ free of rank $2$ over $\mathbb{Q}_\ell \otimes \mathbb{T}_1(N)$, so that $V_\ell(N)/\mathfrak{p}_f V_\ell(N)$ is free of rank $2$ over $\mathbb{Q}_\ell \otimes K_f$
- [Néron model of an abelian variety](../../../../AlgebraicGeometry/abelian-varieties/neron-model.md), for Poincaré's reducibility theorem of its expansion note, which gives the exactness of $V_\ell(B') \to V_\ell(B) \to V_\ell(A) \to 0$ for an exact sequence $B' \to B \to A \to 0$ of abelian varieties

## Expansion

This node is still to be broken down. A good expansion states and links:

- the abelian subvariety $\mathfrak{p}_f J_{\mathbb{Q}}$ and the quotient $A_f$ over $\mathbb{Q}$, with the induced action of
  $\mathbb{T}_1(N)/\mathfrak{p}_f$ and the identification of $(\mathbb{T}_1(N)/\mathfrak{p}_f) \otimes \mathbb{Q}$ with $K_f$ through
  $\theta_f$ (the eigenvalues of the $(T_p)_*$ and $\langle n \rangle_*$ generate $K_f$, as $a_n(f)$ is a polynomial in them);
- Poincaré's reducibility theorem over an algebraically closed field and the resulting exactness of $V_\ell$ on
  exact sequences of abelian varieties in characteristic prime to $\ell$ (Conrad, proof of Theorem 5.14);
- the identification $V_\ell(A_f) = V_\ell(N) / \mathfrak{p}_f V_\ell(N)$, and $\dim V_\ell(A_f) = 2 \dim A_f$, which give 1 and 2;
- the passage from the characteristic polynomial over $\mathbb{Q}_\ell \otimes \mathbb{T}_1(N)$ to the quotient
  $\mathbb{Q}_\ell \otimes K_f$, which gives 3.

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.2, Definition 5.13, p. 68 ("$A_f$ is the quotient of $\operatorname{Pic}^0_{X_1(N)/\mathbf{Q}}$ by
  $\mathfrak{p}_f \subset \mathbf{T}_1(N)$", for a newform $f$, with $\mathbf{T}_1(N)$ acting via the $(\ )_*$-action), and
  Theorem 5.14 (Shimura) with its proof, p. 69 ("We have $\dim A_f = [K_f : \mathbf{Q}]$ and $V_\ell(A_f)$ is free of
  rank 2 over $\mathbf{Q}_\ell \otimes_{\mathbf{Q}} K_f$, with $\mathrm{Frob}_p$ having characteristic polynomial
  $X^2 - (1 \otimes a_p(f)) X + 1 \otimes p \chi_f(p)$ for all $p \nmid N\ell$", proved from Lemma 5.11, Theorem 5.12 and
  the exactness of $V_\ell$, "appeal to Poincaré reducibility").
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section and remark numbers: §12.5, Remark 12.5.6 (for a normalized eigenform $f$
  in $S_2(\Gamma_1(N))$: "we could let $\mathfrak{p} = \ker \theta \cap \mathbf{T}$ and consider the quotient
  $A = J_1(N)/\mathfrak{p}J_1(N)$ [...] the dimension of $A$ is $[K : \mathbf{Q}]$. Moreover
  $\mathrm{Ta}_\ell(A) \otimes_{\mathbf{Z}_\ell} \mathbf{Q}_\ell$ is free of rank two over $K \otimes_{\mathbf{Q}} \mathbf{Q}_\ell$", citing
  Shimura, *On the factors of the jacobian variety of a modular function field*, Theorem 1).
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.7, pp. 44–46 (for an eigenform
  $f$ on $\Gamma$, $I_f = \ker(\lambda_f) \cap \mathbf{T}_{\mathbf{Z}}$, Definition 1.44 "$A_f = J_\Gamma / I_f J_\Gamma$",
  Lemma 1.46 and the sentence after it ("$A_f$ is an abelian variety of dimension $d = [K_f : \mathbf{Q}]$") and Lemma 1.48 ("The module $T_\ell(A_f) \otimes \mathbf{Q}_\ell$ is a free
  module of rank 2 over $K_f \otimes \mathbf{Q}_\ell$")).
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer
  (2005): §6.6, "Eigenforms, Abelian varieties, and Modularity", p. 240, and §9.5, "Galois representations and
  modular forms", p. 386, from the table of contents; the sections themselves were not read.

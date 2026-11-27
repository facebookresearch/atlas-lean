# Pan's theorem: the Fontaine–Mazur conjecture for GL₂ over ℚ for odd p and distinct Hodge–Tate weights

This node is still to be broken down. Let $p$ be an odd prime, $\overline{\mathbb{Q}}_p$ an algebraic closure of
$\mathbb{Q}_p$ and $\iota_p \colon \overline{\mathbb{Q}}_p \to \mathbb{C}$ an isomorphism; fix an embedding
$\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_p$, which makes $G_{\mathbb{Q}_p}$ a decomposition group at $p$ in
$G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Let
$\rho \colon G_{\mathbb{Q}} \to \mathrm{GL}_2(\overline{\mathbb{Q}}_p)$ be a continuous irreducible representation
such that

- $\rho$ is ramified at only finitely many primes: for all other primes $\ell$ it is trivial on the inertia
  groups at $\ell$;
- $\rho|_{G_{\mathbb{Q}_p}}$ is potentially semistable in the sense of Fontaine (its image lies in
  $\mathrm{GL}_2(E)$ for a finite extension $E/\mathbb{Q}_p$, and $E^2$ is then a potentially semistable
  $p$-adic representation of $G_{\mathbb{Q}_p}$; the condition does not depend on $E$);
- $\rho$ is odd: $\det \rho(c) = -1$ for every complex conjugation $c \in G_{\mathbb{Q}}$;
- $\rho|_{G_{\mathbb{Q}_p}}$, which is de Rham, has distinct Hodge–Tate weights: for the embedding
  $\tau \colon \mathbb{Q}_p \to \overline{\mathbb{Q}}_p$ the multiset $\mathrm{HT}_\tau(\rho|_{G_{\mathbb{Q}_p}})$
  consists of two different integers (a condition that does not depend on the sign convention);
- if $p = 3$, the semisimplification of $\bar\rho|_{G_{\mathbb{Q}_p}}$ is not of the form $\eta \oplus \eta\omega$
  for a character $\eta \colon G_{\mathbb{Q}_p} \to \overline{\mathbb{F}}_p^\times$. Here $\omega$ is the mod $p$
  cyclotomic character and $\bar\rho \colon G_{\mathbb{Q}} \to \mathrm{GL}_2(\overline{\mathbb{F}}_p)$ is the
  reduction of $\rho$: $\rho$ preserves a lattice $\mathcal{O}_E^2$ for the ring of integers $\mathcal{O}_E$ of a
  finite extension $E/\mathbb{Q}_p$, and the semisimplification of the reduction modulo the maximal ideal of
  $\mathcal{O}_E$ does not depend on the lattice (Brauer–Nesbitt).

Then $\rho$ comes from a cuspidal eigenform up to twist: there are integers $N \ge 1$ and $k$, a
[cuspidal eigenform](../../modular-forms-q-series/modular-forms/hecke-eigenforms-and-newforms-for-gamma1-n.md)
$f \in S_k(\Gamma_1(N))$ for the Hecke operators away from the level, with Hecke eigenvalues $a_\ell$, and a
continuous character $\psi \colon G_{\mathbb{Q}} \to \overline{\mathbb{Q}}_p^\times$ such that for all but finitely
many primes $\ell$ the representation $\rho \otimes \psi$ is unramified at $\ell$ and
$\operatorname{tr} (\rho \otimes \psi)(\mathrm{Frob}_\ell) = \iota_p^{-1}(a_\ell)$, for a geometric Frobenius
element $\mathrm{Frob}_\ell$ at $\ell$. By the Chebotarev density theorem and the Brauer–Nesbitt theorem this
says that $\rho \otimes \psi$ is isomorphic to the Galois representation attached to $f$ and $\iota_p$. With
arithmetic Frobenius elements the statement is the same, since $\rho^\vee \cong \rho \otimes (\det \rho)^{-1}$.

Fontaine and Mazur conjectured this for every prime $p$ with no condition on the Hodge–Tate weights or on
$\bar\rho$; Pan states the conjecture as Conjecture 1.0.1, and proves this case of it by combining his results
in the residually reducible case with those of Skinner–Wiles, Kisin and Hu–Tan.

A good expansion has pages for: the residually reducible case, Pan's Theorem 1.0.2, and its proof through
the local–global compatibility of completed cohomology (Theorem 3.5.5), Paškūnas' theory and patching at a
one-dimensional prime; the generalizations of Skinner and Wiles's results in the ordinary case (Theorems 5.1.2
and 6.1.2); the residually irreducible cases, due to Kisin and to Hu and Tan, and the case treated in §9; and
the deduction of this theorem from them.

## Depends on

- [Semistable and potentially semistable representations](p-adic-hodge-theory/semistable-representations.md), for potential semistability in the sense of Fontaine
- [de Rham representations](p-adic-hodge-theory/de-rham-representations.md), for Hodge–Tate weights of representations on $\overline{\mathbb{Q}}_p$-vector spaces
- [Hodge–Tate representations](p-adic-hodge-theory/hodge-tate-representations.md), for the Hodge–Tate weights
- [Cyclotomic character and Tate twists](cyclotomic-character-and-tate-twists.md), for the mod $p$ cyclotomic character $\omega$
- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the inertia groups, unramifiedness and the Frobenius elements $\mathrm{Frob}_\ell$
- [Hecke eigenforms and newforms for Γ₁(N)](../../modular-forms-q-series/modular-forms/hecke-eigenforms-and-newforms-for-gamma1-n.md), for cuspidal eigenforms and their Hecke eigenvalues

## Proof depends on

- [Chebotarev density theorem](../adeles-class-field-theory/chebotarev-density-theorem.md), for the step from equal traces of Frobenius at almost all primes to isomorphic semisimple representations, with the Brauer–Nesbitt theorem (Deligne–Serre, Lemma 3.2)

Its proof also uses the inputs listed in the expansion note.

## Sources

- L. Pan, "The Fontaine–Mazur conjecture in the residually reducible case", J. Amer. Math. Soc. 35 (2022),
  1031–1169, doi:10.1090/jams/991, read in the arXiv version arXiv:1901.07166v2 (3 September 2021): §1,
  p. 2, Conjecture 1.0.1 ("Let $p$ be a prime number and $\rho \colon \mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q}) \to
  \mathrm{GL}_2(\overline{\mathbb{Q}_p})$ be a continuous, irreducible representation such that $\rho$ is only
  ramified at finitely many places, the restriction of $\rho$ at the decomposition group at $p$ is potentially
  semi-stable in the sense of Fontaine, $\rho$ is odd, i.e. $\det\rho(c) = -1$ for any complex conjugation $c$.
  Then $\rho$ arises from a cuspidal eigenform up to twist"); p. 5, Theorem 1.0.4 ("Let $p$ be an odd prime and
  $\rho$ be as in conjecture 1.0.1. Assume that $\rho|_{\mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)}$ has
  distinct Hodge–Tate weights; if $p = 3$, the semi-simplification of
  $\bar\rho|_{\mathrm{Gal}(\overline{\mathbb{Q}_p}/\mathbb{Q}_p)}$ is not of the form $\eta \oplus \eta\omega$ for some
  character $\eta$. Then $\rho$ comes from a cuspidal eigenform up to twist"); pp. 6–7, Notation (the isomorphism
  $\iota_p$, geometric Frobenius elements $\mathrm{Frob}_v$, $\omega$ the mod $p$ cyclotomic character, and the
  Hodge–Tate weight of the cyclotomic character $-1$). The journal text was not compared.
- P. Deligne and J.-P. Serre, "Formes modulaires de poids 1", Ann. Sci. École Norm. Sup. (4) 7 (1974),
  507–530, <http://www.numdam.org/item?id=ASENS_1974_4_7_4_507_0>: §3, Lemme 3.2, p. 513 (two semisimple linear
  representations of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ unramified at a set of primes of density $1$, with equal
  traces of Frobenius there in characteristic $0$, are isomorphic; "Cela résulte du théorème de densité de
  Cebotarev", with the determination of a semisimple representation by its traces).
- J.-M. Fontaine and B. Mazur, "Geometric Galois representations", in *Elliptic curves, modular forms, and
  Fermat's last theorem* (Hong Kong, 1993), Ser. Number Theory I, International Press (1995), 41–78, where the
  conjecture is made.

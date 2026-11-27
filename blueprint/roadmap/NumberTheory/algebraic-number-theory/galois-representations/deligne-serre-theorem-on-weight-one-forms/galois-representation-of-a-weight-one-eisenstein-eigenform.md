# Galois representation of a weight-one Eisenstein eigenform

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be an
Eisenstein series of [type $(1, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md), a form whose
decomposition in §1.9 of Deligne–Serre has no cuspidal part, that is an eigenvector of the Hecke operators $T_p$,
$p \nmid N$, with eigenvalues $a_p$. Then there are characters $\chi_1$, $\chi_2$ of
$(\mathbb{Z}/N\mathbb{Z})^*$ with

$$\chi_1 \chi_2 = \varepsilon \qquad \text{and} \qquad a_p = \chi_1(p) + \chi_2(p) \quad \text{for every prime } p \nmid N.$$

Identify each $\chi_i$ with the character of $G = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by composing it with
the homomorphism $G \to (\mathbb{Z}/N\mathbb{Z})^*$ given by the action of $G$ on the $N$-th roots of unity. Then
$\rho = \chi_1 \oplus \chi_2 \colon G \to \mathrm{GL}_2(\mathbb{C})$ is a reducible representation with finite image,
unramified outside $N$, with $\operatorname{Tr}(F_{\rho,p}) = a_p$ and $\det(F_{\rho,p}) = \varepsilon(p)$ for every prime
$p \nmid N$ (unramified and $F_{\rho,p}$ as on
[Semisimple Galois representations with the same Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md)).

This is §8.1 of Deligne–Serre, the case of Théorème 4.1 for an Eisenstein series; they take the eigenvalues from
Hecke.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for forms of type $(1, \varepsilon)$ and the operators $T_p$
- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for the conventions on unramified representations and Frobenius elements

## Proof depends on

- [Cyclotomic fields are unramified at primes not dividing $m$](../../cyclotomic-fields/ramification-and-inertia-in-cyclotomic-fields/is-unramified-in-of-not-dvd.md), applied to $\mathbb{Q}(\mu_N)$, for the unramifiedness of $\chi_1$ and $\chi_2$ outside $N$

## Expansion

This node is still to be broken down. A good expansion states and links:

- Hecke's description of the eigenvalues of the Eisenstein series of type $(1, \varepsilon)$ that are eigenvectors of the
  $T_p$, $p \nmid N$ ([9], p. 690, as cited in Deligne–Serre (1974), p. 525);
- the action of an arithmetic Frobenius element $\mathrm{Frob}_p$ at $p \nmid N$ on the $N$-th roots of unity,
  $\zeta \mapsto \zeta^p$, so that $F_{\chi_i,p} = \chi_i(\mathrm{Frob}_p) = \chi_i(p)$, with the character of $G$ in the
  middle and the Dirichlet character on the right (Deligne–Serre, Remarque 4.4);
- the reduction at the start of §8: by §1.9 a form of type $(1, \varepsilon)$ is the sum of an Eisenstein series and a cusp
  form, the $T_p$ preserve the two summands, so a nonzero summand of an eigenvector is an eigenvector with the same
  eigenvalues, and Théorème 4.1 for $f$ follows from the case of an Eisenstein series when $f$ is not a cusp form and
  from [the cuspidal case](galois-representation-of-a-weight-one-cuspidal-eigenform.md) and
  [its irreducibility](irreducibility-of-the-galois-representation-of-a-weight-one-cusp-form.md) when it is.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §8, opening sentence, and §8.1, p. 525 ("Si f est une
  série d'Eisenstein, il existe des caractères $\chi_1$ et $\chi_2$ de $(\mathbf{Z}/N\mathbf{Z})^*$ tels que
  $\chi_1 . \chi_2 = \varepsilon$ et que $a_p = \chi_1(p) + \chi_2(p)$ pour $p \nmid N$ (cf. [9], p. 690). On prend alors pour ρ
  la représentation réductible $\rho = \chi_1 \oplus \chi_2$"); §1.9, p. 510; Remarque 4.4, p. 514.
- E. Hecke, *Mathematische Werke*, 2nd ed., Vandenhoeck und Ruprecht, Göttingen (1970), p. 690, as cited in
  Deligne–Serre (1974), p. 525; not read.

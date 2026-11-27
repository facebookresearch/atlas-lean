# Irreducibility of the Galois representation of a weight-one cusp form

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be a cusp
form of [type $(1, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) that is an eigenvector of the
Hecke operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Let $\rho \colon G \to \mathrm{GL}_2(\mathbb{C})$,
$G = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, be a representation with finite image, unramified outside $N$, with
$\operatorname{Tr}(F_{\rho,p}) = a_p$ and $\det(F_{\rho,p}) = \varepsilon(p)$ for every prime $p \nmid N$ (unramified and
$F_{\rho,p}$ as on
[Semisimple Galois representations with the same Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md)).
Then $\rho$ is irreducible: no line of $\mathbb{C}^2$ is stable under every $\rho(\sigma)$.

This is §8.7 of Deligne–Serre, the last step of their proof of Théorème 4.1, applied to the representation of
[the cuspidal case](galois-representation-of-a-weight-one-cuspidal-eigenform.md).

Their proof (pp. 526–527). If $\rho$ were reducible it would be the sum of two representations of degree $1$, given by
characters $\chi_1$, $\chi_2$ unramified outside $N$ with $\chi_1 \chi_2 = \varepsilon$ and $a_p = \chi_1(p) + \chi_2(p)$ for
$p \nmid N$. Then

$$\sum |a_p|^2 p^{-s} = 2 \sum p^{-s} + \sum \chi_1(p) \overline{\chi}_2(p) p^{-s} + \sum \chi_2(p) \overline{\chi}_1(p) p^{-s}.$$

As $s \to 1$, $\sum p^{-s} = \log(1/(s-1)) + O(1)$. The character $\chi_1 \overline{\chi}_2$ is not trivial, since otherwise
$\varepsilon = \chi_1^2$ and $\varepsilon(-1) = 1$; so the two last sums are $O(1)$, and

$$\sum |a_p|^2 p^{-s} = 2 \log\bigl(1/(s-1)\bigr) + O(1) \qquad (s \to 1),$$

which contradicts (5.1.1) of [Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md) for $k = 1$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(1, \varepsilon)$ and the operators $T_p$
- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for the conventions on unramified representations and Frobenius elements

## Proof depends on

- [Maschke's theorem](../../../../RepresentationTheory/finite-group-representations/maschke-decomposition.md), applied to the finite image of $\rho$, for the decomposition of a reducible $\rho$ into two characters
- [Rankin's bound for the mean square of Hecke eigenvalues](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md), for the contradiction
- [Non-vanishing of Hecke L-functions on the line Re s = 1](../../../zeta-l-functions/dirichlet-l-functions/hecke-l-function-nonvanishing-on-re-one.md), for $L(1, \chi) \neq 0$ for the nontrivial character $\chi = \chi_1 \overline{\chi}_2$ of finite order
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the action of $G$ on the roots of unity through which a Dirichlet character is a character of $G$: complex conjugation $c$ acts on them by inversion, so $\varepsilon(c) = \varepsilon(-1)$ (Remarques 4.4 and 4.5)

## Expansion

This node is still to be broken down. A good expansion states and links:

- the correspondence between characters of $G$ of finite order unramified outside $N$ and Dirichlet characters of
  conductor divisible only by primes dividing $N$, under which $F_{\chi,p} = \chi(\mathrm{Frob}_p) = \chi(p)$ for
  $p \nmid N$, $\mathrm{Frob}_p$ an arithmetic Frobenius element at $p$, with the character of $G$ in the middle and the
  Dirichlet character on the right, and the value at complex conjugation, $\varepsilon(c) = \varepsilon(-1)$
  (Deligne–Serre, Remarques 4.4 and 4.5);
- the estimates $\sum_p p^{-s} = \log(1/(s-1)) + O(1)$ and, for a nontrivial Dirichlet character $\chi$,
  $\sum_p \chi(p) p^{-s} = O(1)$ as $s \to 1$, from $L(1, \chi) \neq 0$ (Serre, *Cours d'arithmétique*, VI.4.2, as cited in
  Deligne–Serre (1974), p. 526).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §8.7, pp. 526–527 ("Il reste à montrer que ρ est
  irréductible. Si elle ne l'était pas, elle serait somme de deux représentations de degré 1"); Remarques 4.4 and 4.5,
  p. 514; Remarque 3.4, p. 513.
- J.-P. Serre, *Cours d'arithmétique*, Presses Universitaires de France, Paris (1970), VI.4.2, as cited in Deligne–Serre
  (1974), p. 526; not read.

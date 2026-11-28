# Realizability of a semisimple representation over a finite subfield

Let $\Phi$ be a group, $k'$ a finite field and $\varphi \colon \Phi \to \mathrm{GL}_n(k')$ a semisimple representation. Let
$k$ be a subfield of $k'$ containing the coefficients of the polynomials $\det(1 - \varphi(s) T)$ for all $s \in \Phi$.
Then $\varphi$ is realizable over $k$: there is a representation $\rho \colon \Phi \to \mathrm{GL}_n(k)$ such that $\varphi$ is
isomorphic to $\rho$ followed by the inclusion $\mathrm{GL}_n(k) \subseteq \mathrm{GL}_n(k')$, that is, conjugate to it by an
element of $\mathrm{GL}_n(k')$.

This is Lemme 6.13 of Deligne–Serre. Their proof (p. 523): it suffices that $\varphi$ be isomorphic to $\sigma(\varphi)$ for
every automorphism $\sigma$ of $k'$ over $k$, because the Brauer group of a finite field is trivial, so that no Schur
index arises; and $\varphi$ and $\sigma(\varphi)$ are semisimple with the same characteristic polynomials, hence isomorphic.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the theorem that two semisimple representations of a group over a field with the same characteristic polynomials
  are isomorphic (Curtis–Reiner, th. 30.16, as cited in Deligne–Serre (1974), p. 523);
- the descent statement: over a finite field, a semisimple representation isomorphic to all its conjugates under
  $\operatorname{Gal}(k'/k)$ is realizable over $k$, because the Brauer group of a finite field is trivial.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Lemme 6.13 and its proof, p. 523 ("Soit
  φ : Φ → $\mathbf{GL}_n(k')$ une représentation semi-simple d'un groupe Φ sur un corps fini k′. Soit k un sous-corps de k′
  contenant les coefficients des polynômes det(1 − φ(s)T), s ∈ Φ. Alors φ est réalisable sur k").
- C. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*, Interscience, New York
  (1962), th. 30.16, as cited in Deligne–Serre (1974), p. 523; not read.

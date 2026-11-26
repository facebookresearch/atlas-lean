# Kolyvagin's theorem on Heegner points

This node is still to be broken down. Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $K$ be an
imaginary quadratic field of discriminant $D_K \ne -3, -4$ in which every prime factor of $N$ splits, and let
$y_K \in E(K)$ be [the Heegner point](heegner-point-of-an-elliptic-curve.md) for a modular parametrization of $E$.
Assume that $y_K$ has infinite order in $E(K)$. Then

1. the Mordell–Weil group $E(K)$ has rank $1$, so that $y_K$ generates a subgroup of finite index;
2. the [Shafarevich–Tate group](cassels-tate-pairing/elliptic-tate-shafarevich.md) $\text{Ш}(E/K)$ is finite.

Gross also records Kolyvagin's bound on the order of $\text{Ш}(E/K)$ (his Theorem 1.3 (2)); this page does not state
it.

## Expansion

A good expansion follows Gross's account and Darmon's Chapter 10: Heegner points $y_n$ of squarefree conductor $n$
over the ring class fields $K_n$ and their norm relations; Kolyvagin's derivative classes $c(n) \in H^1(K, E_p)$ built
from them, with their local behaviour and their eigenvalue under complex conjugation (Gross, §§3–5, and
[complex conjugation on the Heegner point](complex-conjugation-on-the-heegner-point.md) for $n = 1$); the bound on the
$p$-Selmer group obtained from local Tate duality and the Chebotarev density theorem, first for primes $p$ such that
$\operatorname{Gal}(\mathbb{Q}(E_p)/\mathbb{Q}) \cong \mathrm{GL}_2(\mathbb{Z}/p\mathbb{Z})$ and $p$ does not divide
$y_K$ (Gross, Propositions 2.1 and 2.3), then for the remaining primes; and the passage from Selmer groups to $E(K)$
and $\text{Ш}(E/K)$ through the Kummer sequence $0 \to E(K)/pE(K) \to \operatorname{Sel}(E/K)_p \to \text{Ш}(E/K)_p \to 0$
(Gross, (2.2)).

## Depends on

- [The Heegner point of an elliptic curve over an imaginary quadratic field](heegner-point-of-an-elliptic-curve.md), for $y_K$
- [The Shafarevich–Tate group of an elliptic curve over a number field](cassels-tate-pairing/elliptic-tate-shafarevich.md), for $\text{Ш}(E/K)$

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: Theorem 1.3, p. 236 ("Assume that
  the point $y_K$ has infinite order in $E(K)$. Then (1) the group $E(K)$ has rank 1, (2) the group $\text{Ш}(E/K)$ is
  finite, of order dividing $t_{E/K} \cdot (I_K)^2$."), with the setting of §1, p. 235; Propositions 2.1 and 2.3,
  pp. 237–238, and §§3–5 for the argument.
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 3.21, p. 40 ("If $P_K$ is non-torsion, then the following are true: (1) The
  Mordell-Weil group $E(K)$ is of rank one, so that $P_K$ generates a finite-index subgroup of $E(K)$; (2) The
  Shafarevich-Tate group of $E/K$ is finite."), and Chapter 10.
- V. A. Kolyvagin, *Euler systems* (1988), in *The Grothendieck Festschrift*, Progr. Math., Birkhäuser, Boston, 1990,
  Theorem A. Not read here; cited as Gross cites it (p. 236, and his reference [K1]).

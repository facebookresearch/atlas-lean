# Nadel vanishing for pairs and separation of points by sections

This node is still to be broken down. It covers the forms of Nadel vanishing for pairs on normal
projective varieties and the construction of isolated non-klt centres by which adjoint linear systems
separate points (Angehrn–Siu). Let $X$ be a normal complex projective variety of dimension $n$ and
$\Delta$ an effective $\mathbb{Q}$-divisor on $X$ such that $m(K_X + \Delta)$ is Cartier for some
$m \ge 1$; $(X, \Delta)$ is klt, or lc, at a point if the discrepancies of a log resolution over a
neighbourhood of the point are $> -1$, or $\ge -1$, and the non-klt locus is the set of points where it
is not klt. The targets are:

1. (Nadel vanishing for pairs.) If $N$ is a line bundle with $N \equiv K_X + \Delta + M$ numerically
   for a nef and big $\mathbb{Q}$-line bundle $M$, then the multiplier ideal $\mathcal{J}(X, \Delta)$,
   whose cosupport is the non-klt locus, satisfies $H^i(X, \mathcal{J}(X, \Delta) \otimes N) = 0$ for
   $i > 0$.
2. (Isolated non-klt centres.) If $(X, \Delta)$ is klt, $N_0$ a nef and big $\mathbb{Q}$-line bundle,
   $x$ a closed point, and $c_1, \dots, c_n > 0$ satisfy $c_e^e < (N_0^e \cdot Z)$ for every irreducible
   subvariety $Z \ni x$ of dimension $e \ge 1$ and $\sum_e e / c_e \le 1$, then there is an effective
   $\mathbb{Q}$-divisor $D \equiv N_0$ such that on a neighbourhood of $x$ the pair $(X, \Delta + D)$ is
   lc, klt outside $x$, and not klt at $x$.
3. (Point separation.) Under the hypotheses of 1 with $(X, \Delta)$ klt and $M = N_0$, for two distinct
   closed points $x_1, x_2$ and constants with $c_e^e < (N_0^e \cdot Z)$ for every irreducible $Z$ of
   dimension $e \ge 1$ through $x_1$ or $x_2$ and $\sum_e 2^{1/e} e / c_e \le 1$, some section of $N$
   vanishes at exactly one of $x_1, x_2$.

A good expansion has pages for: multiplier ideals of pairs on normal varieties and the local and global
vanishing theorems for them, deduced from the [Kawamata–Viehweg vanishing
theorem](kawamata-viehweg-vanishing-theorem.md) on a log resolution as for the
[Nadel vanishing theorem](nadel-vanishing-theorem.md) on smooth varieties (Lazarsfeld, the remark on singular
ambient varieties, pp. 5–6, and §2); the construction of divisors with prescribed multiplicities at a point from the
positivity of $(N_0^e \cdot Z)$ and the cutting down of minimal non-klt centres (Angehrn and Siu;
Kollár); and the deduction of 3 from 1 and 2 through the exact sequence of the ideal of the non-klt
locus, as in the analytic version of Demailly's Corollaries (5.12)–(5.13).

## Depends on

- [Multiplier ideal of an effective Q-divisor](multiplier-ideal-of-a-q-divisor.md)
- [Nef and big line bundles](nef-and-big-line-bundles.md)

## Proof depends on

- [Kawamata–Viehweg vanishing theorem](kawamata-viehweg-vanishing-theorem.md)
- [Functorial resolution of schemes of finite type in characteristic zero](functorial-resolution-of-schemes-of-finite-type.md), for log resolutions of pairs on normal varieties

## Sources

- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: the remark on multiplier ideals on singular, normal ambient
  varieties, pp. 5–6; Definition 1.25 (klt pairs); §2.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Corollaries
  (5.12) and (5.13), p. 40 (sections of adjoint bundles from weights with isolated poles).
- U. Angehrn and Y.-T. Siu, "Effective freeness and point separation for adjoint bundles", Invent.
  Math. 122 (1995), 291–308.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) states 1 and 2 in this form, with an ideal sheaf whose cosupport is the
  non-klt locus in place of the multiplier ideal, as
  `GlobalTheory.Published.NadelVanishingAndNonKltDivisor` (the conjunction of `NadelVanishingPair` and
  `IsolatedNonKltDivisor`), and 3 as `GlobalTheory.Published.PointSeparationPair`.

# Atkin–Lehner involutions on a modular parametrization

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, $f$ its newform, $\omega_f = 2\pi i f(z)\,dz$, and
$\varphi \colon X_0(N) \to E$ a
[modular parametrization](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
with $\varphi(\infty) = O$, so that $\varphi^*\omega = c\,\omega_f$ for an invariant differential $\omega$ of $E$ and a
constant $c \ne 0$. Let $Q \mid N$ with $\gcd(Q, N/Q) = 1$, and let $w_Q$ be the Atkin–Lehner involution of $X_0(N)$;
for $Q = N$ it is the Fricke involution $w_N$. Then:

1. $w_Q^*\omega_f = \varepsilon_Q\,\omega_f$ for a sign $\varepsilon_Q \in \{1, -1\}$; for $Q = N$, $\varepsilon_N$ is the
   [Fricke eigenvalue](../../zeta-l-functions/root-number-and-parity/fricke-eigenvalue-of-a-newform.md) $\varepsilon$ of $f$.
2. For every point $x \in X_0(N)(\mathbb{C})$,

    $$\varphi(w_Q x) = \varepsilon_Q \, \varphi(x) + P_Q, \qquad P_Q = \varphi(w_Q \infty),$$

    and $P_Q$ is a point of finite order of $E(\mathbb{Q})$. For $Q = N$, $P_N = \varphi(0)$, the image of the cusp $0$.

Delaunay states item 2 for the parametrization $\tau \mapsto 2\pi i \int_\infty^\tau f(z)\,dz$ of $\mathbb{C}/\Lambda$, with
$\Lambda$ the lattice of periods of $f$, under his standing assumption that the Manin constant is $1$; the argument of the
Expansion gives it for every $\varphi$ as above.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the Atkin–Lehner involutions $w_Q$ of $X_0(N)$ on cyclic $N$-isogenies, which are defined over $\mathbb{Q}$ (Gross and
  Zagier, Chapter I, (2.2) and the paragraph after it), and the sign $\varepsilon_Q$ of $f$ under $w_Q$ (Delaunay, §2:
  $f$ is an eigenform for $W_Q$);
- the constancy of $x \mapsto \varphi(w_Q x) - \varepsilon_Q \varphi(x)$, worked out here: it is a morphism
  $X_0(N) \to E$ that pulls $\omega$ back to $c\,(w_Q^*\omega_f - \varepsilon_Q\,\omega_f) = 0$, so it is constant, equal
  to its value $\varphi(w_Q \infty)$ at the cusp $\infty$;
- the rationality of $P_Q$, as $w_Q$, $\varphi$ and the cusp $\infty$ are defined over $\mathbb{Q}$, and its finite order:
  for $Q = N$ from the [finiteness of the cuspidal class](cuspidal-divisor-of-x0-n-has-finite-order.md), as
  $w_N \infty = 0$; in general by Delaunay's computation of the values of the parametrization at the cusps with a Hecke
  operator $T_p$, $p \equiv 1 \pmod N$ (§1.1, pp. 110–111), which applies to $\varphi$ because $\varphi$ lifts to
  $\tau \mapsto c \cdot 2\pi i \int_\infty^\tau f(z)\,dz$ modulo the lattice of periods of $\omega$.

## Depends on

- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\varphi$ and the constant $c$
- [Fricke eigenvalue of a newform](../../zeta-l-functions/root-number-and-parity/fricke-eigenvalue-of-a-newform.md), for $\varepsilon$ and $w_N^*\omega_f = \varepsilon\,\omega_f$
- [Complex points of $X_0(N)$ as cyclic $N$-isogenies](../heegner-point-construction/complex-points-of-x0-n-as-cyclic-isogenies.md), for the points of $X_0(N)$ on which $w_Q$ acts

## Proof depends on

- [The cuspidal divisor $(0) - (\infty)$ has finite order](cuspidal-divisor-of-x0-n-has-finite-order.md), for $\varphi(0)$ of finite order and $w_N \infty = 0$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- C. Delaunay, *Critical and ramification points of the modular parametrization of an elliptic curve*,
  J. Théor. Nombres Bordeaux 17 (2005), 109–124: §2, p. 112 ("Since $f$ is an eigenform for $W_Q$, we have $f|W_Q = \pm f$, we deduce that:
  $\varphi \circ W_Q = \pm\varphi + P$, where $P \in E(\mathbb{Q})_{\mathrm{tors}}$."), for $Q \mid N$ with
  $\gcd(Q, N/Q) = 1$; §1.1, pp. 110–111, the parametrization by the periods of $f$, its values at the cusps ("this is a
  torsion point") and the assumption "In this paper, we assume that we have $c = 1$" on the Manin constant.
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320: Chapter I, §2, (2.2) and the paragraph after it, p. 227, the involutions $w_d$ of $X_0(N)$ for
  $d \mid N$ with $(d, N/d) = 1$, which form a group of automorphisms of $X_0(N)$ defined over $\mathbb{Q}$.
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2), p. 243 ("Let $\epsilon = \pm 1$ be the eigenvalue of the Fricke involution $w_N$ on the eigenform
  $f = \sum a_n q^n$ associated to the modular curve $E$"), and the proof of Proposition 5.3, p. 243, which uses the case
  $Q = N$ of item 2 at the Heegner points.

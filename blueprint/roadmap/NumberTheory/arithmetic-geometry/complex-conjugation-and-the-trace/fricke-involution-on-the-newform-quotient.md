# The Fricke involution acts on the newform quotient by its eigenvalue

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, $f$ its newform, $\varepsilon \in \{1, -1\}$ the
eigenvalue of the [Fricke involution on $f$](../../zeta-l-functions/root-number-and-parity/fricke-eigenvalue-of-a-newform.md),
and $\pi \colon X_0(N) \to E$ a [modular parametrization](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md)
with $\pi(\infty) = O$. Let $\pi_* \colon J_0(N) \to E$ be the homomorphism it induces on the Jacobian, which sends the
class of a divisor $\sum_i m_i (x_i)$ of degree zero to $\sum_i m_i \pi(x_i)$. Then

$$\pi_* \circ w_N = \varepsilon \, \pi_*,$$

where $w_N$ also denotes the involution of $J_0(N)$ induced by the Fricke involution of $X_0(N)$. Consequently, for
every point $x \in X_0(N)(\overline{\mathbb{Q}})$, $\pi(w_N x) = \varepsilon \, \pi(x) + \pi(w_N \infty)$, and
$\pi(w_N\infty) = \pi(0)$ is a point of finite order of $E(\mathbb{Q})$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the identification of $\pi_*$, up to isogeny, with the quotient of $J_0(N)$ attached to $f$ by
  [Shimura's construction](../../modular-forms-q-series/modular-forms/shimura-abelian-variety-of-an-eigenform.md), and
  the fact that $w_N$, which commutes with the Hecke endomorphisms $\xi_n$ for $(n, N) = 1$, acts on that quotient as on
  the differential $\omega_f$, by $\varepsilon$;
- the last sentence, from the first applied to the divisor $(x) - (\infty)$ and from the
  [finiteness of the cuspidal class](cuspidal-divisor-of-x0-n-has-finite-order.md).

## Depends on

- [Fricke eigenvalue of a newform](../../zeta-l-functions/root-number-and-parity/fricke-eigenvalue-of-a-newform.md), for $\varepsilon$
- [Modular parametrization of an elliptic curve over $\mathbb{Q}$](../../modular-forms-q-series/modular-forms/modular-parametrization-of-an-elliptic-curve.md), for $\pi$

## Proof depends on

- [Shimura's abelian variety attached to a weight-two eigenform](../../modular-forms-q-series/modular-forms/shimura-abelian-variety-of-an-eigenform.md), for the quotient of $J_0(N)$ attached to $f$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md), for the endomorphisms commuting with $w_N$
- [The cuspidal divisor $(0) - (\infty)$ has finite order](cuspidal-divisor-of-x0-n-has-finite-order.md), for $\pi(0)$ of finite order

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2) and the proof of Proposition 5.3, p. 243 ("Let $\epsilon = \pm 1$ be the eigenvalue of the Fricke
  involution $w_N$ on the eigenform $f = \sum a_n q^n$ associated to the modular curve $E$"; "this gives the claim on
  the curve $E$"), where the passage from $X_0(N)$ to $E$ is this statement, used without proof.
- J. Coates, *The work of Gross and Zagier on Heegner points and the derivatives of $L$-series*, Séminaire Bourbaki,
  exp. 635 (1984/85), Astérisque 133–134 (1986), 57–72, <http://www.numdam.org/item?id=SB_1984-1985__27__57_0>: p. 65 (the point "actually lies in $J(\mathbb{Q})$ … This follows easily from the fact that
  $f|_2 w_N = f$, where $w_N(z) = -1/(Nz)$").

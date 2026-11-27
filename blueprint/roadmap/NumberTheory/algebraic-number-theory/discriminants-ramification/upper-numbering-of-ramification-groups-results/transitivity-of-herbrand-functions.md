# Transitivity of Herbrand's functions

Let $L/K$ be a finite Galois extension of complete discretely valued fields whose residue fields are perfect
of characteristic $p > 0$, with group $G$, let $H$ be a normal subgroup of $G$ and $K' \subseteq L$ its fixed
field, and let $\varphi$ and $\psi = \varphi^{-1}$ be the functions of
[Herbrand's functions](herbrand-functions.md) for the extensions $L/K$, $K'/K$ and $L/K'$. Then

$$\varphi_{L/K} = \varphi_{K'/K} \circ \varphi_{L/K'} \qquad \text{and} \qquad \psi_{L/K} = \psi_{L/K'} \circ \psi_{K'/K}.$$

Both sides of the first identity are continuous, piecewise linear and vanish at $0$, so it suffices to compare
their derivatives at a non-integer $u > -1$. With $v = \varphi_{L/K'}(u)$, the derivative of the right side is
$\varphi'_{K'/K}(v) \varphi'_{L/K'}(u) = \bigl(\lvert (G/H)_v \rvert / e_{K'/K}\bigr) \bigl(\lvert H_u \rvert / e_{L/K'}\bigr)$,
and by [Herbrand's theorem](herbrand-s-theorem.md) $(G/H)_v = G_u H/H \cong G_u/H_u$, so this is
$\lvert G_u \rvert / e_{L/K}$, the derivative $\varphi'_{L/K}(u)$. The identity for $\psi$ follows by inverting.

## Depends on

- [Herbrand's functions](herbrand-functions.md), for the functions $\varphi$ and $\psi$ of the three extensions

## Proof depends on

- [Herbrand's functions](herbrand-functions.md), for their continuity and piecewise linearity, $\varphi(0) = 0$, and the derivative $\varphi'(u) = 1/(G_0 : G_u)$ at a non-integer $u$
- [Herbrand's theorem](herbrand-s-theorem.md), for $(G/H)_v = G_u H/H$ with $v = \varphi_{L/K'}(u)$
- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for $H_u = G_u \cap H$ and for the orders of the inertia groups $G_0$, $(G/H)_0$ and $H_0$, which are the ramification indices $e_{L/K}$, $e_{K'/K}$ and $e_{L/K'}$, so that $1/(G_0 : G_u) = \lvert G_u \rvert / e_{L/K}$

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter IV, §3:
  Proposition 15, p. 74 ("The functions $\varphi$ and $\psi$ satisfy the transitivity formulas:
  $\varphi_{L/K} = \varphi_{K'/K} \circ \varphi_{L/K'}$ and $\psi_{L/K} = \psi_{L/K'} \circ \psi_{K'/K}$"), and its
  proof, p. 75; Serre assumes only that the residue extension is separable.

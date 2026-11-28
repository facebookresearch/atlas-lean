# Minimal Weierstrass models and the identity component of the Néron model

Let $R$ be a discrete valuation ring with fraction field $K$, let $E$ be an elliptic curve over $K$,
and let

$$W : \; y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6, \qquad a_1, \dots, a_6 \in R,$$

be a Weierstrass equation of $E$ that is minimal: the valuation of its discriminant $\Delta_W$ is the
least among the Weierstrass equations of $E$ with coefficients in $R$. Let
$\mathcal{W} \subset \mathbb{P}^2_R$ be the closed subscheme defined by the homogenized equation,
$\mathcal{W}^{\mathrm{sm}}$ its open subscheme of points at which $\mathcal{W}$ is smooth over $R$,
$\mathcal{E}$ the [Néron model](../../abelian-varieties/neron-model.md) of $E$ over $R$, with zero section
$\varepsilon$, and $\mathcal{E}^0$ the open subgroup scheme of $\mathcal{E}$ obtained by removing the
non-identity components of its special fibre.

**Theorem.**

1. The morphism $\mathcal{W}^{\mathrm{sm}} \to \mathcal{E}$ that extends the identity of $E$, given by
   the Néron mapping property, factors through $\mathcal{E}^0$ and is an isomorphism
   $\mathcal{W}^{\mathrm{sm}} \cong \mathcal{E}^0$.
2. $\mathcal{E}$ is proper over $R$, that is, $E$ has good reduction, if and only if $\Delta_W$ is a
   unit of $R$.
3. The [invariant differential](invariant-differential-of-a-weierstrass-equation.md)
   $\omega_W = dx / (2y + a_1 x + a_3)$ extends to a generator of the invertible sheaf
   $\Omega^1_{\mathcal{W}^{\mathrm{sm}}/R}$. Hence, through item 1, $\omega_W$ generates the
   $R$-module $\varepsilon^* \Omega^1_{\mathcal{E}/R}$ inside
   $\varepsilon^* \Omega^1_{\mathcal{E}/R} \otimes_R K = H^0(E, \Omega^1_{E/K})$.

## Depends on

- [Néron model of an abelian variety](../../abelian-varieties/neron-model.md), for the Néron model
  $\mathcal{E}$, its mapping property and good reduction
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  for $\omega_W$

## Proof depends on

- [Néron model of an abelian variety](../../abelian-varieties/neron-model.md), for the existence of
  $\mathcal{E}$ and its mapping property, which gives the morphism of item 1
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  for the invariant differential of $W$ and its behaviour under variable changes

## Expansion

This node is still to be broken down. A good expansion states and links:

- abstract integral Weierstrass models over $R$ and the freeness of
  $H^0(\mathcal{W}^{\mathrm{sm}}, \Omega^1_{\mathcal{W}^{\mathrm{sm}}/R})$ (Conrad, Theorem 2.6), with
  the Jacobian-criterion computation that $\omega_W$ is a generator, for item 3;
- the criterion for minimality of a Weierstrass model through $R$-rational maps between Weierstrass
  models, and an integral Weierstrass model $\mathcal{W}'$ with an open immersion
  $\mathcal{E}^0 \hookrightarrow \mathcal{W}'^{\mathrm{sm}}$ (Conrad, Corollary 4.6 and Corollary 4.8,
  as used in the proof of Theorem 5.5), for item 1;
- the geometry of singular Weierstrass cubics over a field, for item 2 and for the type of the special
  fibre of $\mathcal{E}^0$ (Conrad, proof of Theorem 5.5).

## Sources

- B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: Theorem 2.6, p. 3 ($\Omega^1$ of the
  smooth locus of an abstract integral Weierstrass model is globally free); Definition 5.1, Theorem 5.2
  and Example 5.3, p. 13 (good reduction of elliptic curves is equivalent to the minimal Weierstrass
  models having unit discriminant); Theorem 5.4 and Theorem 5.5 with its proof, pp. 14–15 (the smooth
  locus of a minimal Weierstrass model is $N(E)^0$; $N(E)$ is proper if and only if the special fibre
  of the minimal Weierstrass model is smooth).
- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 255, the minimal equation (2) at $v$ gives a
  model for the connected component of the Néron model, more precisely a scheme over
  $\operatorname{Spec}(R_v)$ whose smooth part is a model for $\mathcal{E}^0/R_v$, so that
  $\omega_{\mathcal{E}/R_v}$ has the holomorphic, nonvanishing section
  $\alpha_v = dx_v / (2y_v + a_{1,v} x_v + a_{3,v})$; stated without reference.

# The finite places in Silverman's formula for the Faltings height

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, let $E$ be an elliptic curve over
$L$, and let $\omega$ be the invertible $\mathcal{O}_L$-module of the
[Faltings height of $E/L$](faltings-height-over-the-field-of-definition.md), so that
$\omega \otimes_{\mathcal{O}_L} L = H^0(E, \Omega^1_{E/L})$. Let
$\beta_E = \Delta_W \, \omega_W^{\otimes 12} \in (\omega \otimes_{\mathcal{O}_L} L)^{\otimes 12}$ be the
nonzero element given by any Weierstrass equation $W$ of $E$ over $L$, with discriminant $\Delta_W$
and [invariant differential](invariant-differential-of-a-weierstrass-equation.md) $\omega_W$. For a
maximal ideal $\mathfrak{p}$ of $\mathcal{O}_L$ let $\operatorname{ord}_\mathfrak{p}(\beta_E)$ be the
integer $k$ such that $\beta_E$ generates
$\mathfrak{p}^k \, (\omega^{\otimes 12} \otimes_{\mathcal{O}_L} \mathcal{O}_{L,\mathfrak{p}})$.

**Theorem.** For every maximal ideal $\mathfrak{p}$ of $\mathcal{O}_L$,
$\operatorname{ord}_\mathfrak{p}(\beta_E) = v_\mathfrak{p}(\Delta_{E/L})$, the exponent of
$\mathfrak{p}$ in the [minimal discriminant](minimal-discriminant.md) $\Delta_{E/L}$. Hence

$$\sum_{\mathfrak{p}} \operatorname{ord}_\mathfrak{p}(\beta_E) \log \#(\mathcal{O}_L / \mathfrak{p})
  = \log N_{L/\mathbb{Q}}(\Delta_{E/L}).$$

*Proof* (Silverman, p. 255). Fix $\mathfrak{p}$ and a Weierstrass equation $W_\mathfrak{p}$ of $E$
minimal at $\mathfrak{p}$, with discriminant $\Delta_\mathfrak{p}$ and invariant differential
$\alpha_\mathfrak{p}$, so that $v_\mathfrak{p}(\Delta_\mathfrak{p}) = v_\mathfrak{p}(\Delta_{E/L})$.
The module $\omega \otimes_{\mathcal{O}_L} \mathcal{O}_{L,\mathfrak{p}}$ is the module
$\varepsilon^* \Omega^1$ of the Néron model of $E$ over $\mathcal{O}_{L,\mathfrak{p}}$ (the Néron
model over $\mathcal{O}_L$ localizes), and $\alpha_\mathfrak{p}$ generates it (minimal Weierstrass
models give the identity component of the Néron model); so $\alpha_\mathfrak{p}^{\otimes 12}$
generates $\omega^{\otimes 12} \otimes_{\mathcal{O}_L} \mathcal{O}_{L,\mathfrak{p}}$. Since $\beta_E$
does not depend on the Weierstrass equation,
$\beta_E = \Delta_\mathfrak{p} \, \alpha_\mathfrak{p}^{\otimes 12}$, and
$\operatorname{ord}_\mathfrak{p}(\beta_E) = v_\mathfrak{p}(\Delta_\mathfrak{p})$. Summing over
$\mathfrak{p}$ gives $\log \prod_\mathfrak{p} \#(\mathcal{O}_L/\mathfrak{p})^{v_\mathfrak{p}(\Delta_{E/L})} = \log N_{L/\mathbb{Q}}(\Delta_{E/L})$.

## Depends on

- [Faltings height of an elliptic curve over its field of definition](faltings-height-over-the-field-of-definition.md),
  for $\omega$ and $\operatorname{ord}_\mathfrak{p}$
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  for $\beta_E$
- [Minimal discriminant of an elliptic curve over a number field](minimal-discriminant.md), for
  $\Delta_{E/L}$

## Proof depends on

- [Néron model of an abelian variety over the ring of integers of a number field](../abelian-varieties/neron-model-over-a-ring-of-integers.md),
  item 2, for the localization of $\mathcal{E}$ at $\mathfrak{p}$
- [Minimal Weierstrass models and the identity component of the Néron model](minimal-weierstrass-model-and-neron-model.md),
  item 3, for the generator $\alpha_\mathfrak{p}$
- [The invariant differential of a Weierstrass equation](invariant-differential-of-a-weierstrass-equation.md),
  item 3, for $\beta_E = \Delta_\mathfrak{p} \, \alpha_\mathfrak{p}^{\otimes 12}$

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: proof of Proposition 1.1, p. 255, the minimal
  equation (2) at $v \in M_K^0$ with $v(\Delta_v) = v(\Delta_{E/K})$, the section
  $\beta = \Delta \cdot (dx / (2y + a_1 x + a_3))^{\otimes 12}$, the generator $\alpha_v$ of
  $\omega_{\mathcal{E}/R_v}$, $\beta = \Delta_v \alpha_v^{\otimes 12}$, the contribution
  $\log \#(R_v / R_v \Delta_v) = \log \| N_{K/\mathbb{Q}} \Delta_{E/K} \|_v$ of $v$ to
  $\deg(\omega^{\otimes 12})$, and the total
  $\frac{1}{12 [K : \mathbb{Q}]} \log |N_{K/\mathbb{Q}} \Delta_{E/K}|$ of the finite places in
  $h(E/K)$.

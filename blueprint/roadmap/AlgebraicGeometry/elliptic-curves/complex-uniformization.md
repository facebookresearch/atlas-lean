# Complex uniformization of elliptic curves

A lattice $\Lambda \subset \mathbb{C}$ is a subgroup $\mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$ with
$\omega_1, \omega_2$ linearly independent over $\mathbb{R}$. Its Weierstrass function and invariants are

$$\wp(z; \Lambda) = \frac{1}{z^2} + \sum_{\lambda \in \Lambda \setminus \{0\}} \Bigl( \frac{1}{(z - \lambda)^2} - \frac{1}{\lambda^2} \Bigr), \qquad
g_2(\Lambda) = 60 \sum_{\lambda \in \Lambda \setminus \{0\}} \frac{1}{\lambda^4}, \qquad
g_3(\Lambda) = 140 \sum_{\lambda \in \Lambda \setminus \{0\}} \frac{1}{\lambda^6},$$

and $E_\Lambda$ is the curve $Y^2 = 4X^3 - g_2(\Lambda) X - g_3(\Lambda)$ over $\mathbb{C}$. For
$\tau$ in the upper half-plane $\mathbb{H}$ write $\Lambda_\tau = \mathbb{Z} + \mathbb{Z}\tau$; then
$g_2(\Lambda_\tau)$ and $g_3(\Lambda_\tau)$ are the $g_2(\tau)$ and $g_3(\tau)$ of
[Jacobi's product formula](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md),
and $\Delta(\tau) = g_2(\tau)^3 - 27 g_3(\tau)^2$.

**Theorem.**

1. For every lattice $\Lambda$, $\Delta(\Lambda) = g_2(\Lambda)^3 - 27 g_3(\Lambda)^2 \ne 0$, so
   $E_\Lambda$ is an elliptic curve, and the map
   $z \mapsto (\wp(z; \Lambda), \wp'(z; \Lambda))$, sending the points of $\Lambda$ to the point at
   infinity, induces an isomorphism of complex Lie groups $\mathbb{C}/\Lambda \to E_\Lambda(\mathbb{C})$
   under which the differential $dX/Y$ pulls back to $dz$.
2. Every elliptic curve $E$ over $\mathbb{C}$ is isomorphic to $E_\Lambda$ for some lattice $\Lambda$,
   and to $E_{\Lambda_\tau}$ for some $\tau \in \mathbb{H}$; in particular
   $E(\mathbb{C}) \cong \mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$ as complex Lie groups.
3. For lattices $\Lambda$ and $\Lambda'$, the curves $E_\Lambda$ and $E_{\Lambda'}$ are isomorphic if
   and only if $\mathbb{C}/\Lambda$ and $\mathbb{C}/\Lambda'$ are isomorphic as complex Lie groups, if
   and only if $\Lambda$ and $\Lambda'$ are
   [homothetic](../../Analysis/special-functions/elliptic-functions/homothetic-complex-period-lattices/is-homothetic.md),
   if and only if $j(\Lambda) = j(\Lambda')$, where $j(\Lambda) = 1728\, g_2(\Lambda)^3 / \Delta(\Lambda)$
   is the $j$-invariant of $E_\Lambda$.
4. For $\tau, \tau' \in \mathbb{H}$, $\Lambda_\tau$ and $\Lambda_{\tau'}$ are homothetic if and only if
   $\tau' = (a\tau + b)/(c\tau + d)$ for some integers $a, b, c, d$ with $ad - bc = 1$, that is, for
   some element of $\mathrm{SL}_2(\mathbb{Z})$.

## Depends on

- [Homothetic period pairs](../../Analysis/special-functions/elliptic-functions/homothetic-complex-period-lattices/is-homothetic.md),
  for homothety of lattices
- [Jacobi's product formula for the discriminant of a lattice](../../NumberTheory/modular-forms-q-series/modular-forms/lattice-discriminant-eta-product.md),
  for $g_2(\tau)$, $g_3(\tau)$ and $\Delta(\tau)$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the convergence of the series for $\wp$, its periodicity, evenness and double poles at the points of
  $\Lambda$, and the [elliptic functions](../../Analysis/special-functions/elliptic-functions/is-elliptic-function.md)
  and [elliptic orders](../../Analysis/special-functions/elliptic-functions/pole-sets-and-elliptic-order-of-meromorphic-elli/README.md)
  that show that $\wp$ takes each value twice on $\mathbb{C}/\Lambda$, counted with multiplicity;
- the Laurent expansion of $\wp$ at $0$ and the differential equation
  $\wp'^2 = 4\wp^3 - g_2 \wp - g_3$;
- the nonvanishing of $\Delta(\Lambda)$: the values of $\wp$ at the three half-periods are the three
  distinct roots of $4X^3 - g_2 X - g_3$;
- the bijectivity of $z \mapsto (\wp(z), \wp'(z))$ and the addition law, for item 1;
- the surjectivity of $j$ on lattices, or on $\mathbb{H}$, and the classification of elliptic curves
  over $\mathbb{C}$ by their $j$-invariant, for items 2 and 3;
- the lifting of a holomorphic homomorphism $\mathbb{C}/\Lambda \to \mathbb{C}/\Lambda'$ to
  $z \mapsto cz$ with $c\Lambda \subseteq \Lambda'$, and the change of basis of a lattice, for items 3
  and 4.

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 254, the choice, for each archimedean place $v$,
  of $\tau_v \in \mathbb{H}$ with $E(\bar K_v) \cong \mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_v)$, and the
  modular function $j(\tau)$; p. 255, the Weierstrass equation (3),
  $Y_v^2 = 4X_v^3 - g_2(\tau_v) X_v - g_3(\tau_v)$, parametrized by the Weierstrass $\wp$-function,
  $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau_v) \cong E(\bar K_v)$,
  $z \mapsto (\wp(z, \tau_v), \wp'(z, \tau_v))$, with discriminant
  $\Delta_v = g_2(\tau_v)^3 - 27 g_3(\tau_v)^2 = \Delta(\tau_v)$; p. 256, $dX_v/Y_v$ becomes $dz$ under
  this parametrization. For these standard facts Silverman refers (p. 253) to S. Lang, *Elliptic
  Functions* (1973), S. Lang, *Elliptic Curves: Diophantine Analysis* (1978), J. H. Silverman, *The
  Arithmetic of Elliptic Curves* (1986), and J. Tate, "The arithmetic of elliptic curves", Invent.
  Math. 23 (1974), 179–206, as cited by Silverman.
- P. Deligne, "Preuve des conjectures de Tate et de Shafarevitch [d'après G. Faltings]", Séminaire
  Bourbaki, exposé 616 (1983/84), Astérisque 121–122 (1985), 25–41,
  <http://www.numdam.org/item/SB_1983-1984__26__25_0/>: Exemple 1.4, p. 28, the isomorphism of an
  elliptic curve with a Néron differential with $(\mathbb{C}/\Lambda, dz)$, and its Weierstrass equation
  $Y^2 = 4X^3 - \frac{c_4}{12} X - \frac{c_6}{216}$; Remarque 1.5, p. 28, a function of $\tau$
  invariant under $\mathrm{SL}(2, \mathbb{Z})$ comes from a function of the modular invariant $j$.

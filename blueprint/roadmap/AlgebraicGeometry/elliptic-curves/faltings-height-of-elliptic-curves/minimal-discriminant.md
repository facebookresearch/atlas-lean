# Minimal discriminant of an elliptic curve over a number field

Let $L$ be a number field with ring of integers $\mathcal{O}_L$, and let $E$ be an elliptic curve
over $L$, given by a Weierstrass equation

$$y^2 + a_1 x y + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6, \qquad a_1, \dots, a_6 \in L,$$

with nonzero discriminant $\Delta = \Delta(a_1, \dots, a_6)$, a polynomial with integer coefficients
in the $a_i$. The Weierstrass equations of $E$ are those obtained from this one by the
[variable changes](../weierstrass-curves/equation-map-affine-coordinates-iff.md)
$x = u^2 x' + r$, $y = u^3 y' + u^2 s x' + t$ with $u \in L^\times$ and $r, s, t \in L$.

Let $\mathfrak{p}$ be a maximal ideal of $\mathcal{O}_L$, with normalized valuation $v_\mathfrak{p}$
and local ring $\mathcal{O}_{L,\mathfrak{p}}$. A Weierstrass equation of $E$ is **integral at
$\mathfrak{p}$** if its coefficients lie in $\mathcal{O}_{L,\mathfrak{p}}$, and **minimal at
$\mathfrak{p}$** if it is integral at $\mathfrak{p}$ and the valuation $v_\mathfrak{p}$ of its
discriminant is the least among the Weierstrass equations of $E$ that are integral at $\mathfrak{p}$.
Let $\delta_\mathfrak{p}(E) \ge 0$ be that least valuation. It exists: the change with $u = c^{-1}$
and $r = s = t = 0$ multiplies $a_i$ by $c^i$, so for a suitable nonzero $c \in \mathcal{O}_L$ it
gives an equation with coefficients in $\mathcal{O}_L$, whose discriminant lies in
$\mathcal{O}_L \setminus \{0\}$, and the valuations of the discriminants of integral equations are
nonnegative integers. Since the discriminant of an equation with coefficients in $\mathcal{O}_L$ lies
in only finitely many maximal ideals, $\delta_\mathfrak{p}(E) = 0$ for all but finitely many
$\mathfrak{p}$.

The **minimal discriminant** of $E/L$ is the nonzero integral ideal

$$\Delta_{E/L} = \prod_{\mathfrak{p}} \mathfrak{p}^{\delta_\mathfrak{p}(E)} \subseteq \mathcal{O}_L,$$

so that $v_\mathfrak{p}(\Delta_{E/L})$ is the valuation of the discriminant of any Weierstrass equation
of $E$ minimal at $\mathfrak{p}$. Its norm is
$N_{L/\mathbb{Q}}(\Delta_{E/L}) = \#(\mathcal{O}_L / \Delta_{E/L}) = \prod_\mathfrak{p} \#(\mathcal{O}_L/\mathfrak{p})^{\delta_\mathfrak{p}(E)}$.
It depends only on $E$ up to isomorphism over $L$: an isomorphism over $L$ is a variable change, and
it carries the Weierstrass equations of one curve to those of the other.

## Depends on

- [Variable changes transform the Weierstrass equation](../weierstrass-curves/equation-map-affine-coordinates-iff.md),
  for the Weierstrass equations of $E$ and the variable changes between them

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 254, the minimal discriminant $\Delta_{E/K}$ in
  the list of notation ("this is an integral ideal of $K$"), and Remark 1.2 (3), its computation by
  Tate's algorithm or Laska's algorithm; p. 255, the minimal Weierstrass equation (2) at a finite
  place $v$, with discriminant $\Delta_v$ and $v(\Delta_v) = v(\Delta_{E/K})$; for standard facts on
  elliptic curves Silverman refers (p. 253) to S. Lang, *Elliptic Functions* (1973), S. Lang,
  *Elliptic Curves: Diophantine Analysis* (1978), J. H. Silverman, *The Arithmetic of Elliptic
  Curves* (1986), and J. Tate, "The arithmetic of elliptic curves", Invent. Math. 23 (1974), 179–206,
  as cited by Silverman.
- B. Conrad, "Minimal models for elliptic curves", notes (version of 21 November 2015),
  <http://math.stanford.edu/~conrad/papers/minimalmodel.pdf>: §1, p. 1, the minimal Weierstrass model
  of an elliptic curve over the fraction field of a discrete valuation ring.

# Faltings height of an abelian subvariety

Let $k$ be a number field, $A$ an [abelian variety](../abelian-scheme.md) over $k$ with an ample
invertible sheaf $L$, and $B$ an abelian subvariety of $A$. Let $B^\perp$ be the abelian subvariety
orthogonal to $B$ for $L$: the identity component of the kernel of the composite $\widehat\imath
\circ \phi_L \colon A \to \widehat A \to \widehat B$, where $\phi_L$ is the
[polarization](../polarization.md) attached to $L$ and $\widehat\imath$ the dual of the inclusion
$\imath \colon B \hookrightarrow A$. Then

$$h_F(B) \le h_F(A) + \log h^0(B, L|_B) + \frac{3}{2} \dim B^\perp,$$

where $h_F$ is the [stable Faltings height](faltings-height.md).

Gaudron and Rémond derive it from [Raynaud's estimate](raynaud-isogeny-height-estimate.md) applied
to the addition isogeny $B \times B^\perp \to A$, whose degree $b$ satisfies $b \le h^0(B, L)\,
h^0(B^\perp, L) / h^0(A, L) \le h^0(B, L)^2$, and from the [lower bound of
Bost](bost-lower-bound.md) for $h_F(B^\perp)$; they first state it for their height $h$, with
$(\dim B^\perp) \log \sqrt{2\pi}$ in place of $\frac{3}{2} \dim B^\perp$, and pass to $h_F$ by
bounding $\log(\pi \sqrt 2) \le 3/2$. In the isogeny estimate it bounds the height of the abelian
subvariety given by the period theorem (*Polarisations et isogénies*, p. 2096).

## Expansion

A good expansion has a page for the orthogonal abelian subvariety: that the addition map $B \times
B^\perp \to A$ is an isogeny of degree at most $h^0(B, L)\, h^0(B^\perp, L) / h^0(A, L) \le h^0(B,
L)^2$ (*Théorème des périodes*, §2.2, p. 351, which cites Bertrand, Théorème 3).

## Depends on

- [Stable Faltings height](faltings-height.md)
- [Polarization](../polarization.md), for $\phi_L$
- [Dual abelian variety](../dual-abelian-variety.md), for $\widehat A$, $\widehat B$ and dual
  homomorphisms

## Proof depends on

- [Raynaud's estimate for the Faltings height under isogeny](raynaud-isogeny-height-estimate.md),
  item 1 for the addition isogeny and item 2 for $h_F(B \times B^\perp)$
- [Bost's lower bound for the Faltings height](bost-lower-bound.md), for $h_F(B^\perp) \ge
  -\frac{3}{2} \dim B^\perp$

## Sources

- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
  Helv. 89 (2014), 343–403, <https://doi.org/10.4171/CMH/322>: §2.2, p. 351 (the orthogonal abelian
  subvariety and the degree of the addition isogeny) and §2.3, p. 352 (the bound for $h(B)$ and its
  variant for $h_F(B)$).
- D. Bertrand, *Duality on tori and multiplicative dependence relations*, J. Austral. Math. Soc. Ser.
  A 62 (1997), 198–216: Théorème 3, as cited by Gaudron and Rémond, *Théorème des périodes*, p. 351
  (not read).

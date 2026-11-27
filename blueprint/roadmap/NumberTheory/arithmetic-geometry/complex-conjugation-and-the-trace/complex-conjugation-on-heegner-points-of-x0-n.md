# Complex conjugation on Heegner points of $X_0(N)$

Let $N \ge 1$, let $K \subset \mathbb{C}$ be an imaginary quadratic field of discriminant $D_K \ne -3, -4$ in which every
prime factor of $N$ splits, let $x_1 \in X_0(N)(K_1)$ be the Heegner point of
[the construction](../heegner-point-construction/rationality-of-heegner-points.md), rational over the Hilbert class
field $K_1$, let $\tau$ be complex conjugation, which preserves $K_1$, and let $w_N$ be the Fricke involution of
$X_0(N)$, which sends a cyclic $N$-isogeny $\varphi \colon A \to A'$ to its dual $\varphi' \colon A' \to A$. Then

$$x_1^\tau = w_N(x_1^{\sigma'}) \qquad \text{for some } \sigma' \in \operatorname{Gal}(K_1/K).$$

Gross states this for the Heegner points $x_n$ of every conductor $n$ prime to $N$, over the ring class field $K_n$;
this page is the case $n = 1$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the action of $\tau$ on the CM curves $\mathbb{C}/\mathfrak{a}$, by complex conjugation of the lattice, and the
  identification of $\mathbb{C}/\bar{\mathcal{N}}^{-1} \to \mathbb{C}/\mathcal{O}_K$ with the dual of a Heegner isogeny
  of the same class group orbit, as in Gross, *Heegner points on $X_0(N)$*, §5.

## Depends on

- [Heegner points are rational over the Hilbert class field](../heegner-point-construction/rationality-of-heegner-points.md), for $x_1$ and $K_1$
- [Complex points of $X_0(N)$ as cyclic $N$-isogenies](../heegner-point-construction/complex-points-of-x0-n-as-cyclic-isogenies.md), for the description of $w_N$ on cyclic isogenies

## Proof depends on

- [Galois and Atkin–Lehner action on Heegner points](../heegner-point-construction/galois-and-atkin-lehner-action-on-heegner-points.md), for the transitive action of $W \times \operatorname{Gal}(K_1/K)$ on Heegner points

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: proof of Proposition 5.3, p. 243 ("This follows from the identity [G, §5] $x_n^\tau = w_N(x_n^{\sigma'})$ for
  some $\sigma'$ in $\mathcal{G}_n$.").
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320: Chapter I, §2, (2.1), p. 227 ("The canonical involution $w_N$ of $X$ takes the point $x = (\phi \colon E \to E')$ to
  the point $w_N(x) = (\phi' \colon E' \to E)$ where $\phi'$ is the dual isogeny.").
- B. H. Gross, *Heegner points on $X_0(N)$*, in *Modular forms* (Durham, 1983), Ellis Horwood, Chichester, 1984,
  87–105, §5. Not read here; cited as Gross (1991, p. 243) cites it.

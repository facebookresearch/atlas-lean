# Garland's vanishing theorem for cohomology of high-dimensional expanders

Let $X$ be a pure $d$-dimensional finite simplicial complex, $d \ge 2$, all of whose links of $(d-2)$-faces are connected graphs, and suppose that for every $(i-1)$-face $\tau$, $1 \le i \le d-1$, the link $X_\tau$ has normalized random-walk spectral gap satisfying

$$
\lambda_2(M_\tau) < \frac{1}{i + 1}.
$$

Then the real cohomology vanishes in degrees $1 \le i \le d - 1$: $H^i(X; \mathbb{R}) = 0$. In particular, quotients of Bruhat-Tits buildings of rank at least $2$ over local fields with large residue field have vanishing real cohomology in all intermediate degrees.

## Proof sketch

Write the $i$-th Laplacian of a harmonic cochain $f$ as an average over $(i-1)$-faces $\tau$ of link Laplacians applied to localizations of $f$. Each localized cochain is orthogonal to constants on the link, so the link spectral gap gives a positive lower bound on its energy; summing yields $\langle \Delta f, f \rangle \ge c\langle f, f\rangle$ with $c > 0$, forcing harmonic cochains to vanish.

## Depends on

- [Cochains and the coboundary operator over F_2](../coboundary-and-cosystolic-expansion/cochains-coboundary.md)
- [Link of a face in a weighted complex](link-of-face.md)

## Proof depends on

- [Garland's method: localization of the link Laplacian quadratic form](garland-method.md)

## Sources

- H. Garland, "p-adic curvature and the cohomology of discrete subgroups of p-adic groups", Annals of Mathematics 97 (1973) 375-423.
- W. Ballmann, J. Świątkowski, "On L2-cohomology and property (T) for automorphism groups of polyhedral cell complexes", Geometric and Functional Analysis 7 (1997) 615-645.

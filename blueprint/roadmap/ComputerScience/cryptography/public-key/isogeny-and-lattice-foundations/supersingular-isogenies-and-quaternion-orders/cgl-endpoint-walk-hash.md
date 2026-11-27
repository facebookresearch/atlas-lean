# The Charles–Goren–Lauter walk with endpoint output

The Charles–Goren–Lauter construction reads a fixed-length string of digits as directions for a walk without backtracking in the supersingular $\ell$-isogeny graph from a fixed start vertex, and outputs the $j$-invariant of the end vertex. This page fixes the labelling of edges explicitly and does not include the compression of the output to $\mathbb{F}_p$ that the paper also proposes.

**Parameters.** Primes $p$ and $\ell$ with $\ell\ne p$ and $p\equiv1\pmod{12}$; a length $n\ge1$; for every supersingular $j$-invariant $j$ a fixed [supersingular curve](supersingular-curves.md) $E_j$ with $j(E_j)=j$ (Charles, Goren and Lauter use models over $\mathbb{F}_{p^2}$); a start vertex $j_0$; and an *injective labelling*: for every $j$ and every subgroup $B\subseteq E_j(\bar{\mathbb{F}}_p)$ of order $\ell$, a bijection $\lambda_{j,B}$ from $\{0,\dots,\ell-1\}$ onto the $\ell$ subgroups of order $\ell$ of $E_j(\bar{\mathbb{F}}_p)$ other than $B$, and for the start vertex an injective map $\lambda_{\mathrm{start}}$ from $\{0,\dots,\ell-1\}$ to its $\ell+1$ subgroups of order $\ell$. All isogenies and isomorphisms below are over $\bar{\mathbb{F}}_p$; for $p\equiv1\pmod{12}$ every supersingular curve has [only the automorphisms $\pm1$](../../../../../AlgebraicGeometry/elliptic-curves/supersingular-elliptic-curves/supersingular-automorphisms-when-p-is-one-mod-twelve.md), which fix every subgroup.

**Walk.** The input is a digit string $d=(d_1,\dots,d_n)\in\{0,\dots,\ell-1\}^n$ of the fixed length $n$. Put $v_0=j_0$ and $H_1=\lambda_{\mathrm{start}}(d_1)$. For $i=1,\dots,n$:

1. let $\varphi_i\colon E_{v_{i-1}}\to E_{v_{i-1}}/H_i$ be the [separable isogeny with kernel](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md) $H_i$, put $v_i=j(E_{v_{i-1}}/H_i)$, choose an isomorphism $\iota_i\colon E_{v_{i-1}}/H_i\to E_{v_i}$, and set $\varphi'_i=\iota_i\circ\varphi_i\colon E_{v_{i-1}}\to E_{v_i}$;
2. if $i<n$, let $B_i=\ker\hat\varphi'_i\subseteq E_{v_i}(\bar{\mathbb{F}}_p)$ be the kernel of the [dual](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/dual-isogeny.md) of $\varphi'_i$, a subgroup of order $\ell$, and put $H_{i+1}=\lambda_{v_i,B_i}(d_{i+1})$.

The subgroup $B_i$ does not depend on the choice of $\iota_i$, because two choices differ by $\pm1$, and $H_{i+1}\ne B_i$, so $(\varphi'_i)$ is a [chain without backtracking](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/isogeny-chain-without-backtracking.md). The output is

$$
h(d)=v_n=j\bigl(E_{v_{n-1}}/H_n\bigr)\in\mathbb{F}_{p^2},
$$

and letting the start vertex vary gives a family of such functions. Each step follows one edge of the [supersingular $\ell$-isogeny graph](supersingular-isogeny-graph.md).

For $\ell=2$ the input is a bit string of length $n$, as in Charles, Goren and Lauter, Section 4.2, and the labelling of the two subgroups other than the one back along the dual is by a fixed ordering of the roots of a quadratic. For other $\ell$ the paper converts the input "to a base-$(k-1)$ number" for a $k$-regular graph; such a conversion gives a digit string of fixed length $n$ only with a fixed number of digits including leading zeros, which is the form assumed here. The start labelling $\lambda_{\mathrm{start}}$ uses $\ell$ of the $\ell+1$ edges at $j_0$; this is a convention of this page that makes every step have $\ell$ choices, not one specified by the paper. The paper also maps the output to $\mathbb{F}_p$ by a linear function, so that collisions of that compressed output need not be collisions of $h$.

## Depends on

- [Supersingular elliptic curves and isogenies](supersingular-curves.md)
- [Supersingular l-isogeny graphs](supersingular-isogeny-graph.md)
- [Every finite subgroup is the kernel of a separable isogeny](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [Existence and uniqueness of the dual isogeny](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/dual-isogeny.md)
- [Chain of isogenies without backtracking](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/isogeny-chain-without-backtracking.md)
- [Supersingular curves have only the automorphisms plus or minus one when p is 1 mod 12](../../../../../AlgebraicGeometry/elliptic-curves/supersingular-elliptic-curves/supersingular-automorphisms-when-p-is-one-mod-twelve.md)
- [Counting subgroups of prime-power order in the torsion of an elliptic curve](../../../../../AlgebraicGeometry/elliptic-curves/isogeny-chains-and-supersingular-graphs/number-of-cyclic-subgroups-of-prime-power-torsion.md)
- [Supersingularity is an isogeny invariant](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/supersingularity-is-an-isogeny-invariant.md)

## Proof depends on

- [The kernel of an isogeny has order its separable degree](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/kernel-order-equals-separable-degree.md)
- [Composition, sum and double-dual rules for dual isogenies](../../../../../AlgebraicGeometry/elliptic-curves/isogenies-of-elliptic-curves/properties-of-the-dual-isogeny.md)

## Expansion

A definition. Well-definedness uses facts from the linked pages: each vertex is supersingular, because supersingularity is an isogeny invariant; each curve has exactly $\ell+1$ subgroups of order $\ell$, so the labellings exist; separable isogenies of degree $\ell$ are determined by their kernels up to an isomorphism of the target, so $v_i$ depends only on $H_i$; and the dual of $\varphi'_i$ is separable of degree $\ell$, so its kernel has order $\ell$, and replacing $\iota_i$ by $\varepsilon\circ\iota_i$ replaces that kernel by $\varepsilon(B_i)$, by the composition rule for duals, which is $B_i$ since $\varepsilon=\pm1$.

## Sources

- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 2.2, Section 3, Section 4 and Section 4.2, and the Notation paragraph of Section 5.1.
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Section 13 and Figure 10.
- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Section 3 (the paragraph describing the hash function).

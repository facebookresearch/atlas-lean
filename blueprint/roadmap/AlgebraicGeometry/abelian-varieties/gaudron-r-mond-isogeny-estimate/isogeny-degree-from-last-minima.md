# Isogeny degrees from last minima

Let $K$ be a field of characteristic zero and let $A$, $A'$ and $A_1, \dots, A_t$ be
[abelian varieties](../abelian-scheme.md) over $K$, with integers $n_1, \dots, n_t \ge 1$, such that
each $A_i$ is simple over $K$, $A_i$ and $A_j$ are not isogenous over $K$ for $i \ne j$, and $A$, $A'$
and $A'' = \prod_{i=1}^t A_i^{n_i}$ are isogenous over $K$. Put $g_i = \dim A_i$, $d_i =
\operatorname{rk}_\mathbb{Z} \operatorname{End}_K(A_i)$ and $g = \dim A = \sum_{i=1}^t n_i g_i$. For
an abelian variety $C$ over $K$ let $Z(C) = (C \times \widehat C)^4$, with $\widehat C$ the
[dual abelian variety](../dual-abelian-variety.md). Fix principal polarizations of $Z(A)$, $Z(A')$
and $Z(A_i)$ over $K$, which exist by [Zarhin's trick](../zarhin-trick.md), give $Z(A'') \simeq
\prod_{i=1}^t Z(A_i)^{n_i}$ the product polarization, and let

$$\Lambda = \Lambda\bigl(\operatorname{Hom}_K(Z(A''), Z(A))\bigr), \quad \Lambda' =
\Lambda\bigl(\operatorname{Hom}_K(Z(A''), Z(A'))\bigr), \quad \Lambda_i =
\Lambda\bigl(\operatorname{End}_K(Z(A_i))\bigr)$$

be the last minima for the [Rosati metrics](rosati-metric-on-homomorphisms.md) of these principal
polarizations. Then:

1. There is an [isogeny](../isogenies-of-abelian-schemes.md) $A \to A''$ defined over $K$ of degree
   at most

    $$(16g)^{2g}\, \Lambda^{4g} \prod_{i=1}^t \Lambda_i^{8 n_i^2 g_i d_i}.$$

2. There is a pair of isogenies $\varphi_1 \colon A \to A'$ and $\varphi_2 \colon A' \to A$ defined
   over $K$ with

    $$\max(\deg \varphi_1, \deg \varphi_2) \le (16g)^{4g}\, (\Lambda \Lambda')^{4g} \prod_{i=1}^t
    \Lambda_i^{8 n_i^2 g_i d_i}.$$

Item 2 is Gaudron and Rémond's Proposition 6.3 (3). Item 1 is their Proposition 6.2, an isogeny $A
\to A''$ of degree at most $(16g)^{2g} \Lambda^{4g} \prod_i V_i^{g_i n_i \min(2n_i, 4)}
\widehat{W}_i^{\,2 g_i n_i / d_i}$, combined with their Lemme 6.1, $V_i^a W_i^b \widehat{W}_i^{\,c}
\le \Lambda_i^{4 d_i \max(a/2, b, c)}$, for $a = g_i n_i \min(2n_i, 4)$, $b = 0$ and $c = 2 g_i n_i /
d_i$: then $\max(a/2, c) \le 2 g_i n_i^2$. Here $V_i$, $W_i$ and $\widehat W_i$ are the covolumes of
§6 (p. 2084), which no longer appear in the bound. They use item 1 for the height of $A''$ in the
last step of the isogeny estimate (Lemme 9.4, p. 2100), noting that Proposition 6.2 gives a bound
smaller than the final bound of their §6, $(10g)^{5g} (\Lambda \Lambda')^{4g} \prod_i
\Lambda_i^{8 n_i^2 g_i d_i}$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the volumes $\operatorname{vol}(\operatorname{Hom}_K(A, B))$ and their independence of the
  polarizations (Proposition 2.9 and Corollaire 2.10, pp. 2067–2068);
- the bound $\deg \varphi \le \frac{|\varphi|^{2g}}{(2g)^g} \frac{h^0(A, L)}{h^0(B, M)}$
  (Proposition 2.11, pp. 2068–2069, after Masser and Wüstholz);
- Minkowski's first and second theorems in the weak form of Lemme 3.1 (pp. 2069–2070, after
  Martinet's *Perfect lattices in Euclidean spaces*, Theorem 2.6.8);
- the avoidance lemma 3.2 (p. 2070), which gives an isogeny of degree at most $(2g)^g \frac{h^0(A,
  L)}{h^0(B, M)} \Lambda(\operatorname{Hom}_K(A, B))^{2g}$ from the Siegel avoidance lemma of
  Gaudron and Rémond (*Lemmes de Siegel d'évitement*, Théorème 1.1);
- the isogeny theorem for simple abelian varieties (Proposition 4.1 (1), pp. 2072–2073);
- the class index lemma and the isogenies between an abelian subvariety of $A^N$ and a power of $A$
  (Lemmes 4.8 and 5.3, Proposition 5.4, pp. 2079–2083, after Masser and Wüstholz, *Factorization
  estimates*, and Reiner's *Maximal orders*);
- Lemme 6.1 (p. 2084), with the Hadamard inequality $\operatorname{vol}(\Gamma) \le
  \Lambda(\Gamma)^n$ for a lattice of rank $n$.

## Depends on

- [Rosati metric on lattices of homomorphisms](rosati-metric-on-homomorphisms.md), for the last
  minima $\Lambda$, $\Lambda'$ and $\Lambda_i$
- [Zarhin's trick](../zarhin-trick.md), for the principal polarizations of $Z(A)$, $Z(A')$ and
  $Z(A_i)$
- [Dual abelian variety](../dual-abelian-variety.md), for $\widehat C$
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for isogenies and their degree
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $K$

## Proof depends on

- [Rosati metric on lattices of homomorphisms](rosati-metric-on-homomorphisms.md), for the lattices
  of homomorphisms with their Rosati metrics
- [Zarhin's trick](../zarhin-trick.md), for the principal polarizations, which make the bounds
  independent of the polarizations of $A$ and $A'$
- [Hadamard's determinant inequality](../../../LinearAlgebra/positive-definite-matrices/hadamard-s-inequality-and-determinant-bounds-for/hadamard-s-determinant-inequality/hadamard-determinant-inequality.md),
  for $\operatorname{vol}(\Gamma) \le \Lambda(\Gamma)^n$ in Lemme 6.1

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §6, pp. 2083–2089 (the setting, pp. 2083–2084; Lemme
  6.1 and Proposition 6.2, p. 2084, with the proof of Proposition 6.2, pp. 2084–2085; Proposition
  6.3 (3), p. 2086, with its proof, p. 2087; the final bound of §6, p. 2089); §§2–5 for the lemmas
  of the expansion: Propositions 2.9 and 2.11 and Corollaire 2.10, pp. 2067–2069, Lemmes 3.1 and 3.2,
  pp. 2069–2070, Proposition 4.1, pp. 2072–2073, Lemme 4.8, p. 2079, Lemme 5.3, p. 2082, Proposition 5.4,
  p. 2083; and Lemme 9.4, p. 2100.
- É. Gaudron and G. Rémond, *Lemmes de Siegel d'évitement*, Acta Arith. 154 (2012), 125–136,
  <https://doi.org/10.4064/aa154-2-2>: Théorème 1.1, as cited by Gaudron and Rémond, *Polarisations
  et isogénies*, p. 2070 (not read).

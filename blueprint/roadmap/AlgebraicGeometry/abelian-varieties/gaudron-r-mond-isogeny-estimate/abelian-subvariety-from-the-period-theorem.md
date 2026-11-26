# Abelian subvariety of bounded degree from the period theorem

Let $k$ be a number field, with algebraic closure $\bar k$. For an
[abelian variety](../abelian-scheme.md) $B$ over $k$, write $B$, up to isogeny over $\bar k$, as
$\prod_{i=1}^t B_i^{r_i}$ with $B_i$ simple over $\bar k$ and pairwise non-isogenous, and put

$$\nu(B) = \sum_{i=1}^t \frac{2 (\dim B_i)^2}{\operatorname{rk}_\mathbb{Z}
\operatorname{End}_{\bar k}(B_i)},$$

which depends only on the isogeny class of $B$ over $\bar k$. For an abelian variety $C$ over $k$,
let $Z(C) = (C \times \widehat C)^4$, with $\widehat C$ the
[dual abelian variety](../dual-abelian-variety.md), which has a principal polarization over $k$ by
[Zarhin's trick](../zarhin-trick.md).

Let $A$ and $B$ be abelian varieties over $k$ of dimensions $g$ and $b$, and fix principal
polarizations of $Z(A)$ and $Z(B)$ over $k$. Let $Z = Z(A) \times Z(B)^{128b}$, with the product
principal polarization, and let $p \colon Z \to Z(A)$ and $q_j \colon Z \to Z(B)$, $1 \le j \le
128b$, be the projections. Suppose that $A$ is simple over $k$, that $g \le b$, and that all
endomorphisms of $A \times B$ are defined over $k$. Then there is an abelian subvariety $H$ of $Z$
such that

1. $p(H) = Z(A)$;
2. for every $f \in \operatorname{Hom}_k(Z(A), Z(B))$ there are integers $\ell \in \mathbb{N}
   \setminus \{0\}$ and $m_1, \dots, m_{128b} \in \mathbb{Z}$ with $H \subset \operatorname{Ker}
   \bigl(\ell f \circ p + \sum_{j=1}^{128b} m_j q_j\bigr)$;
3. the degree of $H$ for the polarization of $Z$ is at most

    $$\Bigl( (8b)^{64 b^2} [k : \mathbb{Q}] \max\bigl(1, h_F(A), h_F(B), \log [k :
    \mathbb{Q}]\bigr)^2 \Bigr)^{8 \nu(B)},$$

    where $h_F$ is the [stable Faltings height](../stable-faltings-height/faltings-height.md).

Together with the [bound for the last minimum from an abelian
subvariety](last-minimum-from-an-abelian-subvariety.md), this bounds the last minimum of
$\operatorname{Hom}_k(Z(A), Z(B))$.

## Expansion

If $\operatorname{Hom}_k(A, B) = \{0\}$, then $H = Z(A) \times \{0\}$ works. Otherwise $H$ is the
smallest abelian subvariety of $Z$ whose tangent space at one embedding $\sigma_0$ contains eight
periods built from short periods of $Z(A)_{\sigma_0}$ and $Z(B)_{\sigma_0}$, and the
[period theorem](period-theorem.md), kept at $\sigma_0$ only, bounds its degree (*Polarisations et
isogénies*, pp. 2095–2097). A good expansion has pages for: Lemme 8.1 (for a complex abelian variety
$H$ and a finite set $S \subset \Omega_H$ of periods with $S \not\subset \Omega_{H'}$ for every
strict abelian subvariety $H'$ of $H$, $\dim H \le \operatorname{Card}(S)\, \nu(H)$), with the properties of $\nu$ listed on p. 2091;
Lemme 8.3 (eight of the short periods of $Z(A)_{\sigma_0}$ already determine $Z(A)_{\sigma_0}$);
the transference bound $1 \le \lambda(\Omega_A) \Lambda(\Omega_A) \le 2g\, h^0(A, L)$ for the lattice
of periods (Corollaire 3.6, after Banaszczyk); Lemme 8.4 (the bound $\lVert \varpi_i
\rVert^2_{\sigma_0} \le e^{12.5} b^4 \max(1, h_F(A), h_F(B))$ for the eight periods, through
[Autissier's matrix lemma](autissier-matrix-lemma.md) and the choice of $\sigma_0$); and the
elementary Lemme 8.5 with the final numerical estimates.

## Depends on

- [Stable Faltings height](../stable-faltings-height/faltings-height.md)
- [Zarhin's trick](../zarhin-trick.md), for the principal polarizations of $Z(A)$ and $Z(B)$
- [Dual abelian variety](../dual-abelian-variety.md), for $\widehat C$
- [Polarization](../polarization.md), for principal and product polarizations
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $k$

## Proof depends on

- [Gaudron–Rémond period theorem](period-theorem.md), for the degree of $H$
- [Autissier's matrix lemma](autissier-matrix-lemma.md), with $\varepsilon = 1/8$, for the norms
  of the eight periods (Lemme 8.4)
- [Faltings height of an abelian subvariety](../stable-faltings-height/faltings-height-of-abelian-subvariety.md),
  for $h_F(H) \le h_F(Z) + \log h^0(H, N) + \frac{3}{2} \dim H^\perp$
- [Raynaud's estimate for the Faltings height under
  isogeny](../stable-faltings-height/raynaud-isogeny-height-estimate.md), items 2 and 3, for
  $h_F(Z(A)) = 8 h_F(A)$ and $h_F(Z) = 8 h_F(A) + 2^{10} b\, h_F(B)$

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §8, pp. 2091–2097: the invariant $\nu$, p. 2091;
  Lemme 8.1, pp. 2091–2092; Proposition 8.2, pp. 2092–2093; Lemmes 8.3 and 8.4, pp. 2093–2094; the
  proof of Proposition 8.2 with Lemme 8.5, pp. 2095–2097; $Z(C) = (C \times \widehat C)^4$,
  Corollaire 2.10, p. 2068; Corollaire 3.6, p. 2072.

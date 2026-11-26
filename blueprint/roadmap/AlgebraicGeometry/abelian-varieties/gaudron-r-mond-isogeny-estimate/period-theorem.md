# Gaudron–Rémond period theorem

Let $k$ be a number field and $A$ an [abelian variety](../abelian-scheme.md) of dimension $g \ge 1$
over $k$, with a polarization $L$, the class in the Néron–Severi group of an ample invertible sheaf
on $A$, and let $\deg_L A = (L^g)$ be the degree of $A$ for $L$. For an embedding $\sigma \colon k
\hookrightarrow \mathbb{C}$, let $A_\sigma$ be the complex abelian variety obtained by extension of
scalars, $t_{A_\sigma}$ its tangent space at the origin, $\Omega_{A_\sigma} \subset t_{A_\sigma}$ its
lattice of periods (the kernel of the exponential map), $\lVert \cdot \rVert_{L,\sigma}$ the
hermitian norm on $t_{A_\sigma}$ given by the Riemann form of $L_\sigma$, and $d_L$ the associated
distance. For an abelian subvariety $B$ of $A_\sigma$ different from $A_\sigma$, the **avoidance
minimum** of $B$ is

$$\delta(A_\sigma, L_\sigma, B) = \min \{ d_L(\omega, t_B) : \omega \in \Omega_{A_\sigma} \setminus
\Omega_B \},$$

and the **essential minimum** of $(A_\sigma, L_\sigma)$ is $\delta(A_\sigma, L_\sigma) = \sup_B
\delta(A_\sigma, L_\sigma, B)$, the supremum over all abelian subvarieties $B \ne A_\sigma$; for $B =
\{0\}$ the avoidance minimum is the least norm of a nonzero period. Then

$$\frac{1}{[k : \mathbb{Q}]} \sum_{\sigma \colon k \hookrightarrow \mathbb{C}} \frac{(\deg_L
A)^{1/g}}{\delta(A_\sigma, L_\sigma)^2} \le 50\, g^{2g+6} \max\bigl(1, h_F(A), \log \deg_L A\bigr),$$

where $h_F(A)$ is the [stable Faltings height](../stable-faltings-height/faltings-height.md) of $A$.

This is a sharpened, explicit form of the period theorem of Masser and Wüstholz, which Gaudron and
Rémond derive from Masser and Wüstholz's *Periods and minimal abelian subvarieties* in the form: for a
period $\omega$ of $A_\sigma$ and the smallest abelian subvariety $A_\omega$ whose tangent space
contains $\omega$, $\deg_L A_\omega \le c \max(1, h_F(A), \lVert \omega \rVert^2_{L,\sigma})^\kappa$,
with $c$ depending on $g$, $[k : \mathbb{Q}]$ and $\deg_L A$, and $\kappa$ on $g$. In the proof of
the isogeny estimate it is applied to an abelian subvariety $H$ of a product of principally polarized
abelian varieties, keeping only the term of one embedding (Gaudron and Rémond, *Polarisations et
isogénies*, p. 2095).

## Expansion

The proof is a transcendence argument in the periodic case of linear forms in logarithms, after the
Gel'fond–Baker method in the variant of Philippon and Waldschmidt that extrapolates on derivations,
with an auxiliary section in place of an auxiliary function (*Théorème des périodes*, §4.4,
p. 364). The theorem follows from their key Théorème 4.5 (p. 362), stated with an avoidance minimum
at each embedding, through Corollaire 4.6 (p. 363) and §6.10.1 (p. 381). A good expansion has pages
for: the complex uniformization of abelian varieties and the Riemann form of a polarization (§2.4,
after Mumford and Birkenhake–Lange); the matrix lemma, in the case $g = 1$ and through Proposition 3.6
(p. 357); the bound for the maximal slope of the cotangent space (Proposition 3.10, after
Graftieaux); the analytic interpolation lemma (§5, Proposition 5.1, p. 365); the multiplicity lemma
of Nakamaye (used in Proposition 6.1, p. 369); the Siegel lemma of Bombieri–Vaaler (§6.5, p. 373);
and the slope estimates of §§6.3–6.8 (pp. 370–380).

## Depends on

- [Stable Faltings height](../stable-faltings-height/faltings-height.md)
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $k$
- [Polarization](../polarization.md)

## Proof depends on

- [Autissier's matrix lemma](autissier-matrix-lemma.md), for the matrix lemma of §3 (Théorème 3.1 and
  Proposition 3.6) used in the proof

## Sources

- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
  Helv. 89 (2014), 343–403, <https://doi.org/10.4171/CMH/322>: Théorème 1.2, p. 345 (stated for the
  essential minimum, with the remark on p. 346 that it holds with $\delta(A_\sigma, L_\sigma) =
  \sup_B \delta(A_\sigma, L_\sigma, B)$); Définition 4.1, p. 360 (avoidance and essential minima);
  §2.1, p. 351 (polarizations and $\deg_L A$); §2.4, pp. 352–353 (Riemann form and the norm
  $\lVert \cdot \rVert_{L,\sigma}$); the theorem of Masser and Wüstholz as stated on p. 344; the
  proof in §§4–6, pp. 360–381.
- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §8, p. 2095, where the theorem is restated, under the
  heading Théorème des périodes, and applied.
- D. Masser and G. Wüstholz, *Periods and minimal abelian subvarieties*, Ann. of Math. 137 (1993),
  407–458, as cited by Gaudron and Rémond, *Théorème des périodes*, p. 344 (not read).

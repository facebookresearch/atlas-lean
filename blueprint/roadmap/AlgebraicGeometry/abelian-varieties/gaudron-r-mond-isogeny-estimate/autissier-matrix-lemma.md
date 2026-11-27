# Autissier's matrix lemma

Let $K$ be a number field, $\varepsilon \in \mathopen]0, 1\mathclose[$ a real number and $(A, L)$ a
principally polarized [abelian variety](../abelian-scheme.md) of dimension $g \ge 1$ over $K$. For an
embedding $\sigma \colon K \hookrightarrow \mathbb{C}$, let $\rho(A_\sigma, L_\sigma)$ be the least
norm $\lVert \omega \rVert_{L,\sigma}$ of a nonzero period $\omega$ of the complex abelian variety
$A_\sigma$, for the hermitian norm on its tangent space given by the Riemann form of $L_\sigma$ (the
injectivity diameter, the first minimum of the lattice of periods). Then

$$h_F(A) + \frac{g}{2} \log \frac{2\pi^2}{\varepsilon} \ge \frac{(1 - \varepsilon)\, \pi}{6\, [K :
\mathbb{Q}]} \sum_{\sigma \colon K \hookrightarrow \mathbb{C}} \frac{1}{\rho(A_\sigma, L_\sigma)^2},$$

where $h_F(A)$ is the [stable Faltings height](../stable-faltings-height/faltings-height.md) of $A$
in Faltings' normalization (Autissier's $h_{Fa}$, defined with the metric $\lVert \phi \rVert^2 =
\frac{i^{g^2}}{2^g} \int_{A_\sigma(\mathbb{C})} \phi \wedge \bar\phi$).

It is Autissier's Corollaire 1.4, a simplified form of his Théorème 1.1, which Gaudron and Rémond
restate in their normalization $h(A)$ as Théorème 3.1 of *Théorème des périodes et degrés minimaux
d'isogénies*. They also use Corollaire 1.4 in the proof of their Proposition 3.6 (p. 357), in the
form $T \le \frac{6}{\pi(1 - \varepsilon)} h(A) + \frac{3g}{\pi(1 - \varepsilon)} \log
\frac{2\pi}{\varepsilon}$ for $T = \frac{1}{[K : \mathbb{Q}]} \sum_\sigma \rho(A_\sigma,
L_\sigma)^{-2}$, noting that replacing $h_F(A)$ by $h(A) = h_F(A) + \frac{g}{2} \log \pi$ replaces
$2\pi^2$ by $2\pi$ in Autissier's formula. In the proof of the isogeny estimate it is applied with
$\varepsilon = 1/8$ to the principally polarized abelian varieties $Z(A) = (A \times \widehat A)^4$
and $Z(B)$, of heights $8 h_F(A)$ and $8 h_F(B)$ (Gaudron and Rémond, *Polarisations et isogénies*,
Lemme 8.4).

## Expansion

This node is still to be broken down. A good expansion states and links:

- Autissier's Théorème 1.1, $h_{Fa}(A) \ge \frac{1}{[K : \mathbb{Q}]} \sum_\sigma \bigl(\frac{\pi}{6
  \rho_\sigma^2} + g \log(\kappa \rho_\sigma \sqrt{g})\bigr)$ with $\rho_\sigma = \min(\rho(A_\sigma,
  L_\sigma), \sqrt{\pi/(3g)})$ and $\kappa = \sqrt{3/(2\pi^3 e)}$, restated by Gaudron and Rémond in
  their normalization as Théorème 3.1 (p. 355), from which Corollaire 1.4 follows by $\log u \le u -
  1$ applied to $u_\sigma = \varepsilon\pi/(3g\rho_\sigma^2)$;
- the lower bound of Bost for the height of a principally polarized abelian variety in terms of
  integrals of theta functions that its proof rests on (Autissier's Théorème 3.1, proved in the
  appendix of *Théorème des périodes*, §8, pp. 395–400), and Autissier's preliminaries on lattices
  (§2);
- the complex uniformization and the Riemann form of a polarization.

## Depends on

- [Stable Faltings height](../stable-faltings-height/faltings-height.md)
- [Polarization](../polarization.md), for principal polarizations
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $K$

## Sources

- P. Autissier, *Un lemme matriciel effectif*, Math. Z. 273 (2013), 355–361,
  <https://doi.org/10.1007/s00209-012-1008-x> (the published version was not read); read in the
  version arXiv:1104.5644 (version 1), <https://arxiv.org/abs/1104.5644v1>: Théorème 1.1, p. 1,
  Corollaire 1.4 with its proof, p. 2, the definition of $h_{Fa}$ and Théorème 3.1 (Bost), p. 5.
- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
  Helv. 89 (2014), 343–403, <https://doi.org/10.4171/CMH/322>: Théorème 3.1, p. 355 (Autissier's
  Théorème 1.1 in the normalization $h$); the proof of Proposition 3.6, p. 357 (Corollaire 1.4 in
  that normalization); §8, pp. 395–400.
- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: Lemme 8.4 and its proof, p. 2094, which cites
  Autissier's Corollaire 1.4.

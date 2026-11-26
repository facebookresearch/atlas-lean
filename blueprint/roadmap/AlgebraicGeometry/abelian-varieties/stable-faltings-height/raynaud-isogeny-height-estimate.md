# Raynaud's estimate for the Faltings height under isogeny

Let $k$ be a number field and $A$, $A'$, $A_1$, $A_2$ [abelian varieties](../abelian-scheme.md) over
$k$, and let $h_F$ be the [stable Faltings height](faltings-height.md).

1. If $\varphi \colon A \to A'$ is an [isogeny](../isogenies-of-abelian-schemes.md), then

    $$\lvert h_F(A') - h_F(A) \rvert \le \frac{1}{2} \log \deg \varphi.$$

2. $h_F(A_1 \times A_2) = h_F(A_1) + h_F(A_2)$.
3. $h_F(\widehat A) = h_F(A)$ for the [dual abelian variety](../dual-abelian-variety.md) $\widehat
   A$.

Gaudron and Rémond state these for their height $h(A) = h_F(A) + \frac{g}{2} \log \pi$, $g = \dim A$,
and note that the estimate holds whatever the normalization; the three statements pass from $h$ to
$h_F$ because isogenous abelian varieties, and an abelian variety and its dual, have the same
dimension, and dimensions add in products. In the isogeny estimate they give $h_F(Z(A)) = 8 h_F(A)$
for $Z(A) = (A \times \widehat A)^4$, bound the heights of the abelian varieties isogenous to $A$ that
enter the proof, and, in the last step, give $h_F(A') \le h_F(A) + \frac{1}{2} \log Q$ when an
isogeny $A \to A'$ of degree at most $Q$ exists.

## Expansion

A good expansion follows Raynaud's proofs of his Corollaire 2.1.4 (for 1) and Corollaire 2.1.3 (for
2 and 3), as cited by Gaudron and Rémond, after reading *Hauteurs et isogénies*, which could not be
read here. It needs pages for the semi-abelian models of abelian varieties over number fields that
define the stable height, and for their behaviour under isogenies, products and duality.

## Depends on

- [Stable Faltings height](faltings-height.md)
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for isogenies and their degree
- [Dual abelian variety](../dual-abelian-variety.md)

## Sources

- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
  Helv. 89 (2014), 343–403, <https://doi.org/10.4171/CMH/322>: §2.3, pp. 351–352 (the estimate of
  Raynaud, with the additivity on products and the invariance under duality, for every
  normalization).
- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: the proof of Proposition 8.2, p. 2096, and Lemme 9.4,
  pp. 2100–2101, where it is applied.
- M. Raynaud, *Hauteurs et isogénies*, in *Séminaire sur les pinceaux arithmétiques : la conjecture
  de Mordell*, Exposé VII, Astérisque 127 (1985), 199–234: Corollaires 2.1.3 and 2.1.4, as cited by
  Gaudron and Rémond, *Théorème des périodes*, p. 352 (not read).

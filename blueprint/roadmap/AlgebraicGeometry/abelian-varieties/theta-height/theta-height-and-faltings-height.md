# Pazuki's comparison of the theta height and the Faltings height

This node is still to be broken down. Its statement is exact; its proof is most of Pazuki's
article.

Let $g \ge 1$ be an integer and $r \ge 2$ an even integer. Let $K$ be a number field, $A$ an
[abelian variety](../abelian-scheme.md) of dimension $g$ over $K$, and $L$ an ample line bundle on
$A$ that is [symmetric](../../not-yet-classified/canonical-polarization-data/is-symmetric.md),
$[-1]^* L \cong L$, and defines a principal [polarization](../polarization.md): $\varphi_L \colon A
\to A^\vee$ is an isomorphism. Let $h_\Theta(A, L)$ be the [theta height](theta-height.md) of level
$r$ of the base change of $(A, L)$ to $\overline{\mathbb{Q}}$ along an embedding $K \to
\overline{\mathbb{Q}}$; it does not depend on the embedding, as Galois conjugation preserves the
$\ell^2$-height. Let $h_F(A)$ be the
[stable Faltings height](../stable-faltings-height/faltings-height.md) of $A$, in
Faltings' normalization. Pazuki's Definition 2.1 gives $\omega$ the metrics
$\|\alpha\|_\sigma^2 = \frac{i^{g^2}}{(2\pi)^g} \int_{A_\sigma(\mathbb{C})} \alpha \wedge
\bar\alpha$ of Deligne's normalization, with $(2\pi)^g$ in place of $2^g$, so his stable Faltings
height is

$$h_F^{\mathrm{Del}}(A) = h_F(A) + \frac{g}{2} \log \pi,$$

the height $h(A)$ of Gaudron and Rémond. Put

$$H_\Theta = \max\{h_\Theta(A, L), 1\}, \qquad H_F = \max\{h_F^{\mathrm{Del}}(A), 1\} =
\max\Bigl\{h_F(A) + \frac{g}{2} \log \pi, 1\Bigr\}.$$

Then

$$\Bigl| H_\Theta - \frac{1}{2} H_F \Bigr| \le C_2(g, r) \log \bigl( \min\{H_\Theta, H_F\} + 2
\bigr), \qquad C_2(g, r) = 1000 \, r^{2g} \bigl( \log (r^{2g}) \bigr)^5.$$

This is Pazuki's Corollary 1.3 (2), with both of its inequalities, $H_\Theta - \frac{1}{2} H_F \le
C_2(g, r) \log(\min\{H_\Theta, H_F\} + 2)$ and $\frac{1}{2} H_F - H_\Theta \le C_2(g, r)
\log(\min\{H_\Theta, H_F\} + 2)$, and with the explicit constant he gives. Pazuki states it for an
abelian variety over $\overline{\mathbb{Q}}$ with such a line bundle; every such pair is the base
change of one over a number field, and neither height changes under a finite extension of $K$, so
the two statements agree. Items (1) and (3) of the corollary, the bound $|h_\Theta(A, L) -
\frac{1}{2} h_F^{\mathrm{Del}}(A)| \le C_1(g, r) \log(H_\Theta + 2)$ and the comparison with the
modified Faltings height of Pazuki's Definition 2.2, are not part of this page.

A good expansion follows Pazuki and states and links: his Theorem 1.1, the comparison
$m(r, g) \le h_\Theta(A, L) - \frac{1}{2} h_F^{\mathrm{Del}}(A) - \frac{1}{4 [K : \mathbb{Q}]}
\sum_{\sigma} \log \det (\operatorname{Im} \tau_\sigma) \le M(r, g)$ with explicit $m(r, g)$ and
$M(r, g)$, for period matrices $\tau_\sigma$ in the Siegel fundamental domain $\mathfrak{F}_g$
(which needs pages for $\mathfrak{F}_g$ and the period matrices), proved in §5.2.1 from
Moret-Bailly models (§3, Definitions 3.1 and 3.2, Theorem 3.4) and Lemma 5.2; the bound of
Remark 1.2 on the period term, from Masser's matrix lemma, with $C(g) = \frac{8g}{\pi}(1 + 2g^2
\log(4g))$; item (1) of Corollary 1.3 with $C_1(g, r) = 6 r^{2g} \log(r^{2g})$, also with
$H_\Theta$ and $H_F$ on its left-hand side (Remark 1.5); and Lemma 5.7, which turns that form of
item (1) into item (2).

## Depends on

- [Theta height](theta-height.md), for $h_\Theta(A, L)$
- [Stable Faltings height](../stable-faltings-height/faltings-height.md), for
  $h_F(A)$
- [Is Symmetric](../../not-yet-classified/canonical-polarization-data/is-symmetric.md), for
  symmetric line bundles
- [Polarization](../polarization.md), for principal polarizations
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over a field

## Proof depends on

- [The stable Faltings height is invariant under finite extension](../stable-faltings-height/faltings-height-field-base-change.md),
  for the passage to a number field over which $A$ has a Moret-Bailly model
- [Semistable reduction theorem for abelian varieties](../semistable-reduction/semistable-reduction-theorem.md), for the
  existence of such fields (the remark after Definition 3.2)

## Sources

- F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
  <https://doi.org/10.24033/bsmf.2623>: Corollary 1.3, pp. 21–22; Definition 2.1, §2.2, p. 26 (the
  stable Faltings height, with the metric of Deligne's normalization); Definition 2.6, p. 30 (the
  theta height); the proof of Corollary 1.3 in §5.2.1, pp. 42–43, with Lemma 5.7. The numbering
  agrees with arXiv:0907.1458v2.
- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment.
  Math. Helv. 89 (2014), 343–403, §2.3, p. 352, <https://doi.org/10.4171/CMH/322>, for
  $h_F(A) = h(A) - \frac{g}{2} \log \pi$.

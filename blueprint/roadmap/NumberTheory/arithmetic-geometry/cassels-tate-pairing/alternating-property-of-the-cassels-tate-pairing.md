# The Cassels–Tate pairing is alternating for a polarization coming from a line bundle

Let $K$ be a number field, $A$ an [abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md)
over $K$ with [dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md) $A^\vee$,
and let $\langle\,,\rangle \colon \text{Ш}(K, A) \times \text{Ш}(K, A^\vee) \to \mathbb{Q}/\mathbb{Z}$ be the
[Cassels–Tate pairing](cassels-tate-pairing-of-an-abelian-variety.md). Let $D$ be a $K$-rational divisor on $A$,
$L = \mathcal{O}(D)$ its line bundle, and let
$\varphi_L \colon A \to A^\vee$ be the homomorphism $a \mapsto t_a^* L \otimes L^{-1}$, which is defined over $K$ and
induces $\varphi_L \colon \text{Ш}(K, A) \to \text{Ш}(K, A^\vee)$. Then

$$\langle a, \varphi_L(a) \rangle = 0 \quad \text{for all } a \in \text{Ш}(K, A).$$

So the pairing $(a, b) \mapsto \langle a, \varphi_L(b) \rangle$ on $\text{Ш}(K, A)$ is alternating, and in particular
antisymmetric. For a polarization of $A$ that is defined over $K$ but does not come from a line bundle on $A$ over
$K$, the induced pairing need not be alternating (Poonen–Stoll, §§1 and 10).

Proof, with the [homogeneous space description](homogeneous-space-description-of-the-cassels-tate-pairing.md) of the
pairing (Milne, Remark I.6.11; Poonen–Stoll, Theorem 5 with $c_\lambda = 0$). Let $X$ be a principal homogeneous space
representing $a$ and $P \in X(\bar K)$, so that $\sigma P = P + \alpha(\sigma)$ for a cocycle $\alpha$ representing $a$.
Then $\varphi_L(a)$ is represented by the cocycle $\sigma \mapsto$ the class of $t_{\alpha(\sigma)}^* D - D$ in
$\operatorname{Pic}^0(A_{\bar K})$. Transported to $\operatorname{Pic}^0(X_{\bar K})$ by the trivialization
$Q \mapsto P + Q$, it becomes the class of $D_P - \sigma(D_P)$, where $D_P$ is the translate of $D$ to $X$; this
visibly lifts to a cocycle with values in $\operatorname{Div}^0(X_{\bar K})$, so its image in
$H^2(G_K, \bar K(X)^\times/\bar K^\times)$ is zero, and so is $\langle a, \varphi_L(a) \rangle$.

## Depends on

- [The Cassels–Tate pairing of an abelian variety](cassels-tate-pairing-of-an-abelian-variety.md)
- [Dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for the homomorphism $\varphi_L$ (its item 2)

## Proof depends on

- [The homogeneous space description of the Cassels–Tate pairing](homogeneous-space-description-of-the-cassels-tate-pairing.md)
- [Dual abelian variety](../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee(\bar K) = \operatorname{Pic}^0(A_{\bar K})$ (its item 1)
- [Theorem of the cube, theorem of the square and the seesaw principle](../../../AlgebraicGeometry/abelian-varieties/theorem-of-the-cube.md), for the theorem of the square, by which $t_x^* D - D$ has class in $\operatorname{Pic}^0$ and translations act trivially on $\operatorname{Pic}^0(A_{\bar K})$

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Remark 6.10 (b) (p. 79: "Let $D$ be a divisor on $A$ rational over $K$ … Then
  $\langle c, \varphi_D(c)\rangle = 0$", citing Tate 1962, Theorem 3.3), and the last paragraph of Remark 6.11 with
  footnote 15 (p. 81, the proof, "This condition was omitted in the original"); Milne's $\varphi_D$ sends $a$ to the class
  of $D_a - D$ with $D_a = D + a$, which is $-\varphi_L(a)$ for $L = \mathcal{O}(D)$.
- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §4, the exact sequence (6) (p. 1118, which shows $c_\lambda = 0$ for $\lambda$ in the
  image of $\operatorname{Pic}(A)$), Theorem 5 and its proof (pp. 1120–1121), Corollary 7 (p. 1122), and the
  Introduction (pp. 1110–1111, Tate's theorem and the examples of Section 10).

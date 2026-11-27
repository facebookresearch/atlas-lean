# Negative Pullback

A pullback map on a negative Tate twist along a morphism of schemes $f : Y \to X$, for the given
Tate data `S` and $j \in \mathbb{N}$: a map from the twist $\mathbb{Z}/l(-(j+1))$ on $X$, the
internal Hom from $\mathbb{Z}/l(j+1)$ to $\mathbb{Z}/l(0)$ (`signedTwist`), to the direct image
under $f$ of the same twist on $Y$, compatible with evaluation: for every étale $U \to X$, every
section $\varphi$ of $\mathbb{Z}/l(-(j+1))$ and every section $a$ of $\mathbb{Z}/l(j+1)$ over $U$,
the image of $\varphi$, evaluated over $U \times_X Y$ at the pullback of $a$, is the pullback of
$\varphi(a)$, the pullbacks being the Tate maps `S.tate f`.

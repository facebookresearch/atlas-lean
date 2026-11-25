# Native bundle euler pullback

Euler classes are compatible with pullback: let $k$ be a perfect field, and fix the given
motivic interface data, whose affine-to-Tate comparison has the properties of the canonical one
(`CanonicalAffineSource`). Let $f : X → Y$ be a morphism of smooth $k$-schemes, $G$ a rank-$d$
bundle geometry on a sheaf of modules $M$ on $Y$ and $G'$ a rank-$d$ bundle geometry on $f^* M$.
Then for all Thom classes $t$ of $G$ and $t'$ of $G'$, $f^* e(G, t) = e(G', t')$, where the Euler
class `euler` is the pullback of the Thom class along the zero section.

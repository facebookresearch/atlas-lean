# The Shafarevich–Tate group of an elliptic curve over a number field

Let $E$ be a
Weierstrass curve over a number field $K$ with algebraic closure $\bar K$. This is the group
$\text{Ш}(E/K)$ of classes in the continuous cohomology group $H^1(G_K, E(\bar K))$ whose
restriction to the absolute Galois group $G_{K_v}$ of the completion $K_v$ is zero for every
place $v$ of $K$, finite or infinite.

Here $G_{K_v}$ acts on $\bar K$ through a $K$-embedding of $\bar K$ into an algebraic closure
$\bar K_v$ of $K_v$, and the restriction lies in $H^1(G_{K_v}, E(\bar K))$, with the coefficients
$E(\bar K)$ fixed. The map from there to $H^1(G_{K_v}, E(\bar K_v))$ is injective at every place,
so the group is the same as the one defined with the local groups $H^1(G_{K_v}, E(\bar K_v))$: at
a finite place the map is an isomorphism (Milne, *Arithmetic Duality Theorems*, 2nd ed.,
Remark I.3.10 (a)(ii), p. 47, for the henselization of $K$ at $v$), at a real place it is
injective by Tarski's transfer principle for real closed fields, and at a complex place both
groups are zero.

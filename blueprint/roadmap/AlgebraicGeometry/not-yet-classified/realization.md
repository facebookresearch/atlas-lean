# Finite Toric Coordinates

A realization of the toric variety of a finite fan $F$ in $\mathbb{R}^n$ over a commutative ring
$k$: a $k$-scheme $X$ with, for every cone $\sigma$ of $F$, a $k$-morphism to $X$ from the affine
chart $U_\sigma = \operatorname{Spec} k[\sigma^\vee \cap \mathbb{Z}^n]$ (`affineChart`), such that
these charts are open immersions, compose with the face map $U_\tau \to U_\sigma$ to the chart of
$\tau$ whenever $\tau$ is a face of $\sigma$, cover $X$, and, for any two cones $\sigma$ and $\tau$,
make the square of $k$-schemes formed by the face maps $U_{\sigma \cap \tau} \to U_\sigma$,
$U_{\sigma \cap \tau} \to U_\tau$ and the charts of $\sigma$ and $\tau$ a pullback.

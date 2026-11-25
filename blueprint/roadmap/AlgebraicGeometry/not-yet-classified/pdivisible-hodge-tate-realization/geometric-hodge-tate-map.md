# Geometric Hodge Tate Map

The Hodge–Tate map of a $p$-divisible group over $\mathcal{O}_C$: let $p$ be a prime and $C$ an
algebraically closed complete non-archimedean normed field extension of $\mathbb{Q}_p$ whose norm
extends that of $\mathbb{Q}_p$, $G$ a $p$-divisible group over $\mathcal{O}_C$ with a Cartier dual
tower $D$, $L$ a Lie model of $D$ with cotangent module $\omega$, $P$ a system of integral finite
projections of the Tate points of $G$ (`IntegralProjectionSystem`), and $B$ a comparison of $\omega$
with the finite Cartier cotangents (`CotangentBridge`). Then there is a $\mathbb{Z}_p$-linear map
$T_p G \to \omega$ sending each $x$ to an element whose projection at every level $n$ is the finite
dlog of the integral point $P_n(x)$, together with a $C$-linear map
$T_p G \otimes_{\mathbb{Z}_p} C \to \omega \otimes_{\mathcal{O}_C} C$ sending $c \otimes x$ to $c$
times the image of $x$ (`HodgeTateMap`).

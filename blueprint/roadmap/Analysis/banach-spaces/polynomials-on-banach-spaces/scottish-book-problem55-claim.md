# Mazur's factorisation claim (Scottish Book Problem 55)

The claim that for every real Banach space $E$, every unbounded set $R \subseteq E$ and every
continuous polynomial $W : E \to \mathbb{R}$ that is bounded on the set of points at distance less
than $\varepsilon$ from $R$ for some $\varepsilon > 0$, there are a real normed space $F$, a
polynomial of first degree $\varphi : E \to F$ with $\varphi(R)$ bounded, and a continuous
polynomial $V : F \to \mathbb{R}$ such that $W = V \circ \varphi$. Here a polynomial of first degree
is a continuous affine map $\varphi(x) = L(x) + a$, with $L$ continuous and linear and $a \in F$,
and a continuous polynomial on a real normed space $X$ is a map
$x \mapsto \sum_{j=0}^{n} A_j(x, \dots, x)$ of some finite degree $n$, where each $A_j$ is a
continuous $j$-linear form on $X$ and $A_0$ is a constant, that is, a finite sum of continuous
homogeneous polynomials.

For finite-dimensional $E$ the answer is positive (Auerbach), with $F$ finite-dimensional. The
factorisation cannot in general use a single scalar affine function: on $\mathbb{R}^3$ with $R$ the
first coordinate axis, $W(x) = x_2^2 + x_3^2$ is bounded near $R$, but it is not a polynomial in one
affine function of $x$.

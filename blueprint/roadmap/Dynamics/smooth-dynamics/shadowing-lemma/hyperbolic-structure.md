# Hyperbolic structure

Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism and let
$K \subseteq \mathbb{R}^d$. Write $DF_x$ for the derivative of a map $F$ at $x$, $T^n$ for the
$n$-fold iterate of $T$ and $T^{-n}$ for the $n$-fold iterate of $T^{-1}$. A hyperbolic structure
for $T$ on $K$ consists of the following: $T$ and $T^{-1}$ are $C^1$; $T(K) = K$; to every
$x \in \mathbb{R}^d$ are assigned linear subspaces $E^s(x)$ and $E^u(x)$ of $\mathbb{R}^d$ such that
for every $x \in K$ we have $\mathbb{R}^d = E^s(x) \oplus E^u(x)$, $DT_x(E^s(x)) = E^s(T(x))$ and
$DT_x(E^u(x)) = E^u(T(x))$; and there are real numbers $\lambda$ with $0 < \lambda < 1$ and
$C > 0$ such that for every $x \in K$ and every $n \in \mathbb{N}$,
$\|D(T^n)_x v\| \le C \lambda^n \|v\|$ for all $v \in E^s(x)$ and
$\|D(T^{-n})_x v\| \le C \lambda^n \|v\|$ for all $v \in E^u(x)$.

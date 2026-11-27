# Infinite products for exponentials of Catalan's constant

Let $G$ be the sum of the series
$\sum_{n \ge 0} (-1)^n / (2n+1)^2$ (Catalan's constant). Then, as $m \to \infty$,

$$
\prod_{n=1}^{2m} \left(1 - \frac{2}{2n+1}\right)^{n(-1)^n} \to e^{2G/\pi - 1/2},
$$



$$
\prod_{n=1}^{2m+1} \left(1 - \frac{2}{2n+1}\right)^{n(-1)^n} \to e^{2G/\pi + 1/2},
$$

and

$$
\left(\frac{\prod_{k=0}^{m-1} (4k+3)^{4k+3}}{\prod_{k=0}^{m-1} (4k+1)^{4k+1}}\right)^2
\frac{(4m+3)^{2m+1}}{(4m+1)^{6m+1}} \to e^{4G/\pi}.
$$

The products $\prod_{k=0}^{m-1} (4k+3)^{4k+3}$ and $\prod_{k=0}^{m-1} (4k+1)^{4k+1}$ are the
source's $3^3 \cdot 7^7 \cdots (4m-1)^{4m-1}$ and $1^1 \cdot 5^5 \cdots (4m-3)^{4m-3}$.

Proof: Following Kachi and Tzermias, Proposition (catalan), dominated convergence reduces the
product limit to the cosecant integral. The substitutions $x = \pi u/2$ and $x = 2 \arctan t$,
followed by the arctangent power series, evaluate it in terms of $G$.

## Sources

- Yasuyuki Kachi and Pavlos Tzermias, "Infinite Products Involving ζ(3) and Catalan's Constant," Journal of Integer Sequences 15 (2012), Article 12.9.4, Proposition, equations, lines 147–165, https://cs.uwaterloo.ca/journals/JIS/VOL15/Tzermias/tzermias2.tex

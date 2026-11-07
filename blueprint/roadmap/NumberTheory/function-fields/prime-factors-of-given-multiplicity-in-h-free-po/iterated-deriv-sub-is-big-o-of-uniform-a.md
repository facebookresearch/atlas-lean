# Derivatives at $z = 1$ of uniform approximations

Let $r > 0$, let $D$ be the open disk of
radius $r$ centred at $1$ in $\mathbb{C}$, and let $f$ and $G_n$ ($n \in \mathbb{N}$) be complex
functions analytic on $D$. Suppose there is a real constant $C$ such that
$|G_n(z) - f(z)\, n^{z-1}| \le C\, n^{\operatorname{Re} z - 2}$ for all $n \ge 1$ and all
$z \in D$. Then for every $k \in \mathbb{N}$ and every $\varepsilon > 0$, as $n \to \infty$,

$$G_n^{(k)}(1) - \frac{d^k}{dz^k}\big(f(z)\, n^{z-1}\big)\Big|_{z=1} = O(n^{\varepsilon - 1}).$$

This is the paper's Lemma 1, a corrected version of Lalín and Zhang's Lemma 3.2; Equation (11) is
the case $k = 1$. The paper's "analytic at $z = 1$" with an error term "in a neighborhood of
$z = 1$" is read as analyticity on a fixed disk on which the bound holds with one constant for all
$n \ge 1$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Lemma 1 (`integers-2025-A9-lem-1`).

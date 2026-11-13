# Asymptotic expansion of Ramanujan's factorial series, for every $x$

Let $x$ be a complex
number. For natural numbers $j$ let
$f(x, j) = e^{-x} \sum_{k=0}^{\infty} \frac{(k+1)^j x^{k+1}}{k!}$, and for complex $z$ let
$\psi(x, z) = \sum_{j=0}^{\infty} t_j$, where
$t_j = \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ when the denominator is nonzero and
$t_j = 0$ otherwise. Let $\varepsilon$ be a real number with $0 < \varepsilon < \pi$, and let
$S_\varepsilon$ be the set of complex $z$ whose principal argument satisfies
$-\pi + \varepsilon \le \arg z \le \pi - \varepsilon$. Then for every natural number $N$,

$$\psi(x, z) - \sum_{j=0}^{N} \frac{(-1)^j f(x, j)}{z^{j+1}} = O\left(\frac{1}{z^{N+2}}\right)$$

as $|z| \to \infty$ with $z \in S_\varepsilon$.

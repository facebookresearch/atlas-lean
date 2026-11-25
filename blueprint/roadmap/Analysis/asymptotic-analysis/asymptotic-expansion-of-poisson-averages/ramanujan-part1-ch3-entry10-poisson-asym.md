# Ramanujan's asymptotic expansion of Poisson averages

Let $M \ge 1$ be an integer,
$\varphi : \mathbb{R} \to \mathbb{C}$ and $G : \mathbb{R} \to \mathbb{R}$ functions, $A \ge 1$ a
real number and $F$ a finite set of natural numbers. Write $\varphi^{(n)}$ for the $n$-th
iterated derivative of $\varphi$ and $S_2(n, k)$ for the 2-associated Stirling numbers of the
second kind. Assume that there are $C \ge 0$ and $p \in \mathbb{N}$ such that
$|\varphi(x)| \le C x^p$ and $|G(x)| \le C x^p$ for all sufficiently large $x$; that $G(x) \ge 1$
for all sufficiently large $x$; and that for every integer $m \ge 1$ and all sufficiently large
$x$, the derivatives $\varphi^{(0)}, \dots, \varphi^{(m-1)}$ are differentiable at $x$ and
$|\varphi^{(m)}(x)| / m! \le G(x) (A / x)^m$. Then, as $x \to \infty$,

$$e^{-x} \sum_{j \in \mathbb{N} \setminus F} \frac{x^j}{j!} \varphi(j) - \varphi(x) -
\sum_{k=2}^{M} \sum_{n=k}^{2k-2} S_2(n, n + 1 - k) \, x^{n-k+1} \frac{\varphi^{(n)}(x)}{n!}
= O\left(\frac{G(x)}{x^M}\right).$$

Proof: Taylor expansion on the central Poisson range is combined with the associated-Stirling
central-moment identity from Comtet; Berndt's route and even-moment tails control the remainder.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 10, printed pp. 57-58 / PDF pp. 67-68.

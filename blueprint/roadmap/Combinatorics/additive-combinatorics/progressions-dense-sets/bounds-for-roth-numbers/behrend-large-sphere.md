# Behrend's lemma: some sphere contains many lattice points of a cube

Let $n$ and $d$ be natural numbers. There is a natural number $k$ such that the set of points
$x = (x_1, \dots, x_n) \in \{0, 1, \dots, d - 1\}^n$ with $x_1^2 + \dots + x_n^2 = k$ has at least

$$\frac{d^n}{n d^2}$$

elements, where the quotient is taken in the real numbers with the convention that it is $0$ when
$n d^2 = 0$, that is, when $n = 0$ or $d = 0$; in those cases the statement holds trivially.

For $n, d \ge 1$ this is the pigeonhole principle: the sum of squares of a point of the cube takes
one of the $n (d - 1)^2 + 1 \le n d^2$ values $0, 1, \dots, n (d - 1)^2$, so one of them is taken by at
least $d^n / (n (d - 1)^2 + 1)$ of the $d^n$ points. Behrend used such a sphere, which contains no
three-term arithmetic progression because the ball is strictly convex, to build large sets of
integers without three-term arithmetic progressions, reading the coordinates of its points as digits
in a large base.

## Sources

- Y. Zhao, *Graph Theory and Additive Combinatorics: Exploring Structure and Randomness*, Cambridge
  University Press, 2023, author's version <https://yufeizhao.com/gtacbook/gtacbook.pdf>: §2.5,
  Theorem 2.5.1 (Behrend's construction) and its proof, p. 71, where for the cube $[m]^d$ of points with
  coordinates in $\{1, \dots, m\}$ the pigeonhole principle gives $L \in [d m^2]$ with at least
  $m^d / (d m^2)$ points on the sphere $x_1^2 + \dots + x_d^2 = L$; the same count applies to the cube
  $\{0, \dots, m - 1\}^d$.
- F. A. Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proc.
  Natl. Acad. Sci. USA 32 (1946), 331–332, <https://doi.org/10.1073/pnas.32.12.331>, the original
  construction, as cited by Zhao.

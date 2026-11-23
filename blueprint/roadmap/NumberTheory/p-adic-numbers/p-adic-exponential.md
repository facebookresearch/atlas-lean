# The p-adic exponential on a neighbourhood of zero

Let $K$ be a finite extension of $\mathbb{Q}_p$, with normalized valuation $\mathrm{ord}_K$, ring of integers
$\mathcal{O}_K$ and unit group $U_K = \mathcal{O}_K^\times$. The exponential series

$$\exp(x) = \sum_{k \ge 0} \frac{x^k}{k!}$$

converges for $\mathrm{ord}_K(x) > \mathrm{ord}_K(p) / (p - 1)$. There is an open subgroup $V$ of the
additive group $\mathcal{O}_K$ on which $\exp$ converges and defines an isomorphism of topological groups
from $V$ onto an open subgroup of $U_K$, whose inverse is given by the logarithm series

$$\log(y) = \sum_{k \ge 1} (-1)^{k+1} \frac{(y - 1)^k}{k}.$$

Since $\mathcal{O}_K$ and $U_K$ are compact, $V$ and $\exp(V)$ have finite index in $\mathcal{O}_K$ and in
$U_K$.

For $K = \mathbb{Q}_p$ the convergence comes from Legendre's formula
$\mathrm{ord}_p(k!) = (k - s_p(k)) / (p - 1)$, where $s_p(k)$ is the sum of the base-$p$ digits of $k$: the
terms $x^k / k!$ tend to $0$ exactly when $\mathrm{ord}_p(x) > 1 / (p - 1)$.

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: the proof of Lemma III.2.4 (the convergence region
  and the isomorphism of an open neighbourhood of $0$ onto an open neighbourhood of $1$ with inverse
  $\log$), used again in the proof of Proposition VII.6.8.
- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>: Example 7.29 (convergence of $\exp$ on
  $\mathbb{Q}_p$).

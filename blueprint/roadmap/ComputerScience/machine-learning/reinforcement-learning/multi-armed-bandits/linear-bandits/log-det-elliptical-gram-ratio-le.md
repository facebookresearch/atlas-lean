# Determinant ratio of the Gram matrix

Let $d \ge 1$, let $V_0 \in \mathbb{R}^{d \times d}$
be symmetric positive definite, let $L \ge 0$, let $a_0, a_1, \ldots \in \mathbb{R}^d$ be numbered
from $0$ with $\lVert a_k \rVert_2 \le L$ for $k < n$, and let
$V_t = V_0 + \sum_{k < t} a_k a_k^{\mathsf T}$. Then

$$\log \frac{\det V_n}{\det V_0}
  \le d \log\Big(\frac{\operatorname{trace} V_0 + n L^2}{d \det(V_0)^{1/d}}\Big).$$

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 19.4, second inequality (divided by $2$), with the actions numbered from $0$. <https://tor-lattimore.com/downloads/book/book.pdf>

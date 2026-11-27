# Capped elliptical potential and the determinant ratio

Let $V_0 \in \mathbb{R}^{d \times d}$
be symmetric positive definite, let $a_0, a_1, \ldots \in \mathbb{R}^d$ be numbered from $0$ and let
$V_k = V_0 + \sum_{j < k} a_j a_j^{\mathsf T}$. Then for every $n$

$$\sum_{k < n} \min\big(1, a_k^{\mathsf T} V_k^{-1} a_k\big) \le 2 \log \frac{\det V_n}{\det V_0}.$$

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 19.4, first inequality, with the actions numbered from $0$. <https://tor-lattimore.com/downloads/book/book.pdf>

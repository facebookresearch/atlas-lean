# From the determinant gain to the capped potential

Let $V_0 \in \mathbb{R}^{d \times d}$ be
symmetric positive definite, let $a_0, a_1, \ldots \in \mathbb{R}^d$ be numbered from $0$, and let
$V_k = V_0 + \sum_{j < k} a_j a_j^{\mathsf T}$ and $q_k = a_k^{\mathsf T} V_k^{-1} a_k$. If, for
some $n$, $\sum_{k < n} q_k / (1 + q_k) \le \log \det V_n - \log \det V_0$, then

$$\sum_{k < n} \min(1, q_k) \le 2 \log \frac{\det V_n}{\det V_0}.$$

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), adapted from the proof of Lemma 19.4, which bounds $\min(1, u)$ by $2 \log(1 + u)$; here it is bounded by $2u / (1 + u)$ for $u \ge 0$, and the sum of the $q_k / (1 + q_k)$ by the hypothesis. <https://tor-lattimore.com/downloads/book/book.pdf>

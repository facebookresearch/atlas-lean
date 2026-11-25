# Elliptical potential lemma

Let $d \ge 1$, let $V_0 \in \mathbb{R}^{d \times d}$ be symmetric positive definite, let $L \ge 0$ and let $a_1, \dots, a_n \in \mathbb{R}^d$ satisfy $\lVert a_t \rVert_2 \le L$, and let $V_t = V_0 + \sum_{s \le t} a_s a_s^{\mathsf T}$. Then

$$\sum_{t=1}^n \min\big(1, \lVert a_t \rVert_{V_{t-1}^{-1}}^2\big) \le 2 \log \frac{\det V_n}{\det V_0} \le 2d \log\Big(\frac{\operatorname{trace} V_0 + n L^2}{d \det(V_0)^{1/d}}\Big).$$

## Proof

Use $\min(1, u) \le 2 \log(1 + u)$ for $u \ge 0$ and $\det V_t = \det V_{t-1} \,(1 + \lVert a_t \rVert_{V_{t-1}^{-1}}^2)$, and telescope. For the second inequality, the AM–GM inequality on
the eigenvalues gives $\det V_n \le (\operatorname{trace} V_n / d)^d$, and $\operatorname{trace} V_n \le \operatorname{trace} V_0 + n L^2$.

## Related topics

- [Stochastic linear bandits and LinUCB regret](stochastic-linear-bandits-and-linucb-regret.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Lemma 19.4. <https://tor-lattimore.com/downloads/book/book.pdf>

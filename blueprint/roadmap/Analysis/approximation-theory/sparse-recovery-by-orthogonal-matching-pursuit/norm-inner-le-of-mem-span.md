# Greedy selection bound

Let $\varphi_1, \dots, \varphi_m$ be vectors (the optimal atoms) in an inner product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $K = \operatorname{span}\{\varphi_i\}$, and let $\psi$ be another vector. Let $a \in \mathbb{K}^m$ satisfy $\sum_i a_i \varphi_i = P_K \psi$. When the atoms are linearly independent, $a = \Phi^{+}\psi$. If $r \in K$ and $|\langle\varphi_i, r\rangle| \le M$ for every $i$, then

$$|\langle \psi, r\rangle| \le \|a\|_1\, M .$$

Indeed $\langle\psi, r\rangle = \langle P_K\psi, r\rangle = \sum_i \bar a_i \langle\varphi_i, r\rangle$. With $M = \max_i |\langle\varphi_i, r\rangle|$ this bounds Tropp's greedy selection ratio $\rho(r) = \|\Psi^* r\|_\infty / \|\Phi^* r\|_\infty$ by $\max_\psi \|\Phi^{+}\psi\|_1$.

## Sources

- J. A. Tropp, Greed is good: algorithmic results for sparse approximation, IEEE Trans. Inform. Theory 50 (2004), 2231–2242, DOI 10.1109/TIT.2004.834793, proof of Theorem 3.1 (the ratio (7) and the bound that follows it).

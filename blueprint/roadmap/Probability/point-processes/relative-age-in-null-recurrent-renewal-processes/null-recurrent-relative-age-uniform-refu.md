# The relative age need not become uniform

Let $X_0, X_1, \dots$ be independent, identically distributed, strictly positive recurrence times that are non-lattice ($P(X_0 \in d\mathbb Z) < 1$ for every $d > 0$) with $\mathbb E X_0 = \infty$, and let $S_k = X_0 + \dots + X_{k-1}$. At time $t$, with $S_k \le t < S_{k+1}$, the relative age is $U_t = (t - S_k)/X_k$. The answer is negative: for some such recurrence times and some $u \in [0, 1]$, $P(U_t \le u)$ does not tend to $u$ (Blanchet, Glynn and Thorisson; Angus and Ding).

## Sources

- H. Thorisson, Some Open Probability Problems, Problem 1.1; resolution: J. Angus and Y. Ding, On the ratio of current age to total life for null recurrent renewal processes, Statist. Probab. Lett. (2020), https://www.sciencedirect.com/science/article/pii/S0167715220300481; first found by J. Blanchet, P. Glynn and H. Thorisson, On the limiting ratio of current age to total life for null recurrent renewal processes, arXiv:1503.08374, Angus-Ding, main results and Concluding remarks: if the inter-arrival survival function is regularly varying with exponent -α, 0 ≤ α ≤ 1, and the mean is infinite, then A(t)/C(t) ⇒ U^{1/α} with U uniform (lattice or not), "a definitive answer to the problem posed in Thorisson (2011)"; Blanchet-Glynn-Thorisson, Theorem 1 (non-arithmetic, regularly varying density, α ∈ (0, 1)), https://arxiv.org/abs/1503.08374.

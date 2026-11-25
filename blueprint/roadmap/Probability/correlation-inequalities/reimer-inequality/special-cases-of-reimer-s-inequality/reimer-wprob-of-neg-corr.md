# Reimer's inequality for negatively correlated events

Let $E$ be a finite set and $\varphi : E \times \{0,1\} \to \mathbb{R}$ a nonnegative weight ($\varphi_x(b) \ge 0$; no normalisation is needed), with $P_\varphi(S) = \sum_{\omega \in S} \prod_x \varphi_x(\omega(x))$. If $A, B \subseteq \{0,1\}^E$ are [negatively correlated](negatively-correlated.md) under $\varphi$, then

$$P_\varphi(A \mathbin{\square} B) \le P_\varphi(A)\, P_\varphi(B),$$

since $A \mathbin{\square} B \subseteq A \cap B$.

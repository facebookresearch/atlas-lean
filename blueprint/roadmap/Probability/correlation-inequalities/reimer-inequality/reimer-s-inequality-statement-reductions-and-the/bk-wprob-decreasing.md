# BK inequality for decreasing events under product weights

Let $E$ be a finite set and $\varphi : E \times \{0,1\} \to \mathbb{R}$ a product probability weight ($\varphi_x(b) \ge 0$, $\varphi_x(0) + \varphi_x(1) = 1$), with $P_\varphi(S) = \sum_{\omega \in S} \prod_x \varphi_x(\omega(x))$. If $A, B \subseteq \{0,1\}^E$ are decreasing, then

$$P_\varphi(A \mathbin{\square} B) \le P_\varphi(A)\, P_\varphi(B).$$

It follows from the [BK inequality for product weights](../../harris-fkg-bk/van-den-berg-kesten-inequality/bk-wprob-general.md) by flipping all coordinates.

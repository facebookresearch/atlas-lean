# Reimer's inequality for two lower families

Let $\alpha$ be a finite set and $w : \alpha \times \{0,1\} \to \mathbb{R}$ a product probability weight ($w_x(b) \ge 0$, $w_x(0) + w_x(1) = 1$). Let $\mathcal{A}, \mathcal{B}$ be lower sets of subsets of $\alpha$ (families closed under taking subsets) and $E_{\mathcal{A}}, E_{\mathcal{B}}$ their [events](family-event.md). Then

$$P_w(E_{\mathcal{A}} \mathbin{\square} E_{\mathcal{B}}) \le P_w(E_{\mathcal{A}})\, P_w(E_{\mathcal{B}}),$$

where $P_w(S) = \sum_{\omega \in S} \prod_x w_x(\omega(x))$. This is the BK inequality for decreasing events.

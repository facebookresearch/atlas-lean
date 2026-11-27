# Slice inequalities in the one-coordinate BK induction step

Let $n \in \mathbb{N}$ and $\psi : \{0,\dots,n-1\} \times \{0,1\} \to \mathbb{R}$ a product probability weight ($\psi_i(b) \ge 0$, $\psi_i(0) + \psi_i(1) = 1$), with $P_\psi(S) = \sum_{\omega \in S} \prod_i \psi_i(\omega_i)$. Let $A, B \subseteq \{0,1\}^{\{0,\dots,n\}}$ be increasing and let $A_0, A_1, B_0, B_1 \subseteq \{0,1\}^{\{0,\dots,n-1\}}$ be their [slices](../../harris-fkg-bk/van-den-berg-kesten-inequality/slice.md) at the first coordinate. Then

$$P_\psi(A_0 \mathbin{\square} B_0) \le P_\psi\big((A_0 \mathbin{\square} B_1) \cap (A_1 \mathbin{\square} B_0)\big)$$

and

$$P_\psi\big((A_0 \mathbin{\square} B_1) \cup (A_1 \mathbin{\square} B_0)\big) \le P_\psi(A_1)\, P_\psi(B_1).$$

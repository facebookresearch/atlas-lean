# Reimer's inequality

Let $n \in \mathbb{N}$ and $\varphi : \{0,\dots,n-1\} \times \{0,1\} \to \mathbb{R}$ a product probability weight on $\{0,1\}^n$: $\varphi_i(b) \ge 0$ and $\varphi_i(0) + \varphi_i(1) = 1$ for all $i, b$. Write $P(S) = \sum_{\omega \in S} \prod_i \varphi_i(\omega_i)$. Then for all events $A, B \subseteq \{0,1\}^n$, not necessarily monotone,

$$P(A \mathbin{\square} B) \le P(A)\, P(B),$$

where $A \mathbin{\square} B$ is the event that $A$ and $B$ occur on disjoint sets of coordinates ([disjoint occurrence](../harris-fkg-bk/van-den-berg-kesten-inequality/disjoint-occurrence.md)). This was conjectured by van den Berg and Kesten.

## Sources

- D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000), 27–32.

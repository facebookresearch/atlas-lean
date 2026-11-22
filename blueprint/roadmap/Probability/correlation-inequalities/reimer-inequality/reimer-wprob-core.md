# Reimer's inequality, product-weight form

For every $n \in \mathbb{N}$, every weight $\varphi : \{0,\dots,n-1\} \times \{0,1\} \to \mathbb{R}$ with $\varphi_i(b) \ge 0$ and $\varphi_i(0) + \varphi_i(1) = 1$, and all events $A, B \subseteq \{0,1\}^n$,

$$P_\varphi(A \mathbin{\square} B) \le P_\varphi(A)\, P_\varphi(B),$$

where $P_\varphi(S) = \sum_{\omega \in S} \prod_i \varphi_i(\omega_i)$. This is the [statement of Reimer's inequality](reimer-s-inequality-statement-reductions-and-the/reimer-wprob-core.md) used as the hypothesis of the reductions; it is the same assertion as [Reimer's inequality](reimer-inequality.md).

## Sources

- D. Reimer, *Proof of the van den Berg–Kesten conjecture*, Combin. Probab. Comput. 9 (2000), 27–32.

# Moulin's iterative-pruning mechanism

Given a cost-sharing scheme $\xi$ and bids $b \in \mathbb{R}^A$, *Moulin's mechanism* starts with $S_0 = A$ and sets $S_{k+1} = \{ j \in S_k : \xi(S_k, j) \le b_j\}$ until $S_{k+1} = S_k$; it then serves the final set $S$ and charges each served agent $\xi(S, j)$ and every other agent $0$. Agents have quasilinear utilities $u_j q_j - p_j$ with binary service $q_j \in \{0, 1\}$.

## Depends on

- [Cross-monotonic γ-budget-balanced cost-sharing scheme](cross-monotonic-budget-balanced-cost-sharing-scheme.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
- Herve Moulin and Scott Shenker, "Strategyproof Sharing of Submodular Costs: Budget Balance versus Efficiency", Economic Theory, 2001.

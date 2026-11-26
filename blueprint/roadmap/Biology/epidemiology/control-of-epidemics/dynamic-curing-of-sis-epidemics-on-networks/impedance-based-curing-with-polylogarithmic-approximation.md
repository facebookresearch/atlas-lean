# Impedance-based dynamic curing of SIS epidemics on networks

Let $G = (V, E, w)$ be an undirected graph on $n$ nodes with edge weights $w_{uv} \in [0,1]$, weighted degrees $d_u = \sum_v w_{uv}$ and maximum degree $d_{\max}$. In the networked SIS process $I(t) \subseteq V$, a susceptible node $v$ becomes infected at rate $\sum_{u \in I(t)} w_{uv}$, and an infected node $u$ is cured at rate $\rho_u(t) \ge 0$ chosen by a controller subject to the budget $\sum_u \rho_u(t) \le r$. For a bag $A \subseteq V$ let $c(A) = \sum_{u \in A,\, v \notin A} w_{uv}$. A *crusade* from $A$ to $\emptyset$ is a sequence $A = p_0 \supset p_1 \supset \dots \supset p_k = \emptyset$ removing one node at a time; its *width* is $z(p) = \max_i c(p_i)$. The *impedance* of $A$ is $\delta(A) = \min_p z(p)$, and the *cutwidth* of $G$ is $\mathcal{W} = \delta(V)$.

**Theorem.**

1. There is a polynomial-time algorithm that, for a bag $A$ with $|A| = k$, outputs a crusade $p$ from $A$ to $\emptyset$ with $\delta(A) \le z(p) \le O(\log^2 k)\,\delta(A)$.
2. If the curing budget satisfies $r \ge \max\{\alpha\,\mathcal{W} \log^2 n,\ 8 d_{\max} \log n\}$ for a suitable absolute constant $\alpha$, a polynomial-time curing policy that cures along such a crusade drives the epidemic to extinction in expected time $O(n \log^2 n / r)$.
3. With demographic groups $V_1,\dots,V_\ell$ ($\ell$ fixed) and checkpoints requiring each group's share among cured nodes to stay within a factor $\gamma$ of its initial share, the same $O(\log^2 k)$ approximation holds for the $\gamma$-fair impedance with one checkpoint, and a $2\gamma$-fair crusade within $O(\log^2 k)$ of the $\gamma$-fair impedance exists for doubling checkpoint sequences $\tau_i - \tau_{i-1} \ge \tau_{i-1}$.

## Expansion

Following the CURE policy of Drakopoulos, Ozdaglar and Tsitsiklis, the controller cures the infected set in a fixed order; along a crusade of width $z$, the total infection pressure on the remaining set is at most $z$, so a budget that dominates $z$ by a logarithmic margin makes the number of infected nodes a supermartingale with negative drift. Computing the impedance exactly is NP-hard; the approximation builds the crusade by recursive balanced cuts, each costing $O(\log k)$ times the optimum, over $O(\log k)$ levels. Fairness is enforced by first partitioning into $\gamma$-fair parts via tree embeddings and dynamic programming on trees.

## Sources

- Yuhao Yi, Liren Shan, Shijie Wang, Philip E. Paré and Karl H. Johansson, *Dynamic Curing and Network Design in SIS Epidemic Processes*, arXiv:2211.06028, Theorems 1, 2, 3 and 4 (section "Curing Algorithms"). <https://doi.org/10.48550/arXiv.2211.06028> Published version: 2024 IEEE 63rd Conference on Decision and Control (CDC) (2024) 4556–4561, <https://doi.org/10.1109/cdc56724.2024.10886502>.

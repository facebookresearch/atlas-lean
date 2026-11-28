# Graph characterization and minimal observability of conjunctive Boolean networks

**Setting.** A *conjunctive Boolean network* (CBN) on state variables $X_1, \dots, X_n \in \{0,1\}$ updates synchronously by

$$
X_i(k+1) = \bigwedge_{j \in N_{\mathrm{in}}(X_i)} X_j(k),
$$

where $N_{\mathrm{in}}(X_i)$ is the set of in-neighbours of $X_i$ in the dependency graph $G$. A set of nodes is measured directly (the *directly observable* nodes, the sensors), giving outputs $y(k)$. The CBN is *observable* if the initial state $X(0)$ is uniquely determined by the outputs $y(0), y(1), \dots$.

**Properties.**
- *$O_1$:* every non-directly-observable node $X_i$ is the unique in-neighbour of some other node $X_j$, i.e. $N_{\mathrm{in}}(X_j) = \{X_i\}$.
- *$O_2$:* every cycle of $G$ consisting only of non-directly-observable nodes contains a node $X_i$ that is the unique in-neighbour of some node $X_j$ not on the cycle.

**Theorem.**
1. A CBN is observable if and only if it satisfies $O_1$ and $O_2$.
2. Equivalently, a CBN is observable if and only if its dependency graph can be partitioned into disjoint *observed paths*: ordered node sets ending at a directly observable node in which every earlier node is not directly observable and is the unique in-neighbour of the next node (shift registers read at their last cell).
3. *(Minimal observability.)* The problem of choosing a minimum number of additional directly observable nodes that makes a given CBN observable is solved exactly by a polynomial-time algorithm.
4. For conjunctive Boolean control networks (CBNs with inputs), observability on $[0, N]$ is defined by setting all inputs to $1$; since $\mathrm{AND}(1, X_1, \dots, X_k) = \mathrm{AND}(X_1, \dots, X_k)$, the analysis and the minimal observability algorithm apply to the simplified CBN.

## Proof sketch

If $X_j$ has the single in-neighbour $X_i$, then $X_j(k+1) = X_i(k)$, so observing $X_j$ one step later reveals $X_i$; chains of such copy relations propagate information backwards from sensors along observed paths. A node that is never the sole input of anything is masked by the AND with other inputs (a $0$ elsewhere hides its value), so it must be measured directly, which is property $O_1$. Cycles are the delicate case: a cycle of unmeasured nodes whose information only circulates inside the cycle can rotate its pattern without changing the outputs, unless some node exits the cycle as the sole input of an outside node, which is property $O_2$. Since testing observability of general Boolean networks is NP-hard, the conjunctive structure is what makes the polynomial-time sensor placement possible.

## Related topics

- [Gene regulatory network dynamics](../README.md)

## Sources

- Eyal Weiss and Michael Margaliot, "A Polynomial-Time Algorithm for Solving the Minimal Observability Problem in Conjunctive Boolean Networks", *IEEE Transactions on Automatic Control* 64 (2019), 2727–2736, <https://doi.org/10.1109/tac.2018.2882154>. Preprint version: arXiv:1706.04072 (2017), Definitions 1–3, Theorem 1, Proposition 1, Corollary 1, Theorem 2, <https://doi.org/10.48550/arXiv.1706.04072>.

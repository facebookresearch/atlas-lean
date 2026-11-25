# Round-robin allocation is envy-free up to one good

Let finitely many indivisible goods be allocated to finitely many agents, at least one, with additive valuations $v_i(S) = \sum_{g \in S}v_i(g)$, $v_i(g) \ge 0$. Agents pick in rounds in a fixed cyclic order, each taking a good of highest value to them among those remaining (ties broken in any way), until no goods remain. The result is envy-free up to one good: for all agents $i, j$, either $j$'s bundle is empty or there is a good $g$ in it with $v_i(A_i) \ge v_i(A_j \setminus \{g\})$. Proof: if $i$ picks before $j$ in each round, $i$'s $k$-th pick is worth at least $j$'s $k$-th pick to $i$; if $j$ picks first, $i$'s $k$-th pick is worth at least $j$'s $(k+1)$-th pick, so removing $j$'s first pick removes the envy.

## Sources

- I. Caragiannis, D. Kurokawa, H. Moulin, A. D. Procaccia, N. Shah and J. Wang, "The unreasonable fairness of maximum Nash welfare", *ACM Transactions on Economics and Computation* 7(3), 2019, Section 1, discussion of the draft (round-robin) mechanism, <https://www.cs.toronto.edu/~nisarg/teaching/2556s22/papers/mnw.pdf>

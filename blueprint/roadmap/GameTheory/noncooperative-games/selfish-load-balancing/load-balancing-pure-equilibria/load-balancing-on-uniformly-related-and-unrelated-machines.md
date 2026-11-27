# Load balancing on uniformly related and unrelated machines

In a *load-balancing game on uniformly related machines*, finitely many jobs $i$ with weights $w_i \ge 0$ each choose one of finitely many machines $j$ with speeds $s_j > 0$; the load of machine $j$ under assignment $A$ is $\ell_j(A) = \sum_{i : A(i) = j} w_i / s_j$, each job pays the load of its machine, and the social cost is the makespan $\max_j \ell_j(A)$. On *unrelated machines* job $i$ has an arbitrary processing time $p_{ij} \ge 0$ on machine $j$. Identical machines are the case $s_j = 1$. The optimal makespan over all assignments is denoted $\mathrm{OPT}$.

## Depends on

- [Pure Nash equilibrium of the load balancing game](../is-pure-nash.md)
- [Makespan](../makespan.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.

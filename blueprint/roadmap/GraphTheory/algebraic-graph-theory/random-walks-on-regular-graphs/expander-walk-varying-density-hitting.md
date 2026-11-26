# Expander walks with varying target densities: the product hitting bound

Let $G$ be a regular multigraph on a finite nonempty set $V$ with labels $L$ and spectral expansion $\lambda$. Start a walk at a uniform vertex $v_0$ and take $t$ steps along independent uniform labels, visiting $v_0, \dots, v_t$. For any sets $B_0, \dots, B_t \subseteq V$ of densities $\beta_i = |B_i|/|V|$,

$$\Pr[\forall i \le t:\ v_i \in B_i] \le \sqrt{\beta_0}\, \prod_{i=1}^{t} \sqrt{\beta_i + \lambda^2}.$$

For a single set $B$ of density $\beta$ and any $\lambda' \ge \lambda$ (for instance a degree-normalized eigenvalue bound $\lambda'/d$ of the source), $\Pr[\forall i \le t: v_i \in B] \le (\beta + \lambda'^2)^{(t+1)/2}$.

## Proof sketch

The probability is $\langle 1_{B_0}, W P_1 W P_2 \cdots W 1_{B_t}\rangle$ with $P_i$ multiplication by $1_{B_i}$. For a function $g$ supported on $B_i$, $\|W g\|^2$ splits into its mean part, at most $\beta_i \|g\|^2$, and its mean-zero part, at most $\lambda^2\|g\|^2$, and dualizing via self-adjointness bounds each masked step by $\sqrt{\beta_i + \lambda^2}$; the first factor is $\|1_{B_0}\| = \sqrt{\beta_0}$.

## Depends on

- [Probability of an event for a random walk on a regular graph](../../graph-families-and-operations/expander-graphs/walk-prob.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Hitting property of expander walks](../../graph-families-and-operations/expander-graphs/hitting-property-of-expander-walks.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Chapters 7-8, public draft (March 2007), 2007.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
- M. Ajtai, J. Komlos, E. Szemeredi, "Deterministic Simulation in LOGSPACE", Proceedings of the 19th Annual ACM Symposium on Theory of Computing, 1987.
- N. Kahale, "Eigenvalues and Expansion of Regular Graphs", Journal of the ACM, 1995.

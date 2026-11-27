# Lower bound for Dyck reachability on bidirected graphs

In the class of separable pointer algorithms for which R. E. Tarjan proved the union-find lower bound, every algorithm that computes Dyck reachability on bidirected graphs, in the sense of [Dyck reachability](dyck-reachability.md), with $n$ nodes and $m \ge n$ edges takes time $\Omega(m + n \cdot \alpha(n))$ in the worst case, where $\alpha$ is the inverse Ackermann function. So within that model the bound of [the almost-linear algorithm](dyck-reachability-on-bidirected-graphs-in-almo.md) is optimal. Chatterjee et al. state the bound without naming the model; on a random-access machine the separated union-find instances of the proof can be solved in linear time by computing connected components.

**Proof idea.** A sequence of union operations followed by find operations on a universe $X$ is encoded as a bidirected graph with a node $z_i$ for the $i$-th union $\mathrm{Union}(x_i, y_i)$ and edges labeled with one closing parenthesis from $z_i$ to $x_i$ and $y_i$; two elements of $X$ are Dyck-reachable from each other exactly when the unions put them in one set. A faster reachability algorithm would beat the lower bound for such separated union-find sequences.

## Depends on

- [Dyck reachability](dyck-reachability.md)
- [Dyck reachability on bidirected graphs in almost-linear time](dyck-reachability-on-bidirected-graphs-in-almo.md)

## Expansion

This page becomes ready once this prerequisite is stated:

- A lower bound for separable pointer algorithms on union-find sequences in which every find follows every union, in the regime the reduction uses: for some constant $c$, sequences with $m \le c\,n$ operations on $n$ elements that require $\Omega(n \cdot \alpha(n))$ time, or a precise two-parameter bound shown to apply to these separated sequences (proof prerequisite; the source reduces it to R. E. Tarjan, "A class of algorithms which require nonlinear time to maintain disjoint sets", *Journal of Computer and System Sciences* 18(2):110–127, 1979, Theorem 4.4). A bound of the form $\Omega(m \cdot \alpha(n))$ for all $m$ cannot hold: keeping a member list per set and a representative pointer per element costs $O(n^2)$ in total for the at most $n - 1$ successful unions and $O(1)$ per find, which is $O(m)$ once $m \ge n^2$.

## Sources

- K. Chatterjee, B. Choudhary and A. Pavlogiannis, "Optimal Dyck reachability for data-dependence and alias analysis", *Proceedings of the ACM on Programming Languages* 2(POPL):30, 2018, <https://arxiv.org/abs/1910.00241>, Section 3.3: the Separated Union-Find problem, Lemma 3.8, the union graph $G_{\sigma_1}$ and Figure 4, Theorem 3.9 and Corollary 3.10.

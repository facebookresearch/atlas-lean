# The Cooper–Harvey–Kennedy dominance algorithm

Let $G$ be a finite control-flow graph with entry node $n_0$ in which every node is reachable from $n_0$, and number its nodes in postorder of a depth-first search from $n_0$, so that $n_0$ has the largest number. The algorithm keeps an array $\mathrm{doms}$, initially undefined except $\mathrm{doms}[n_0] = n_0$, and repeats passes until a pass changes nothing. In each pass it visits the nodes $b \ne n_0$ in reverse postorder:
- it starts from one predecessor of $b$ whose entry is already defined;
- it combines it with every other predecessor $p$ whose entry is defined, by $\mathrm{intersect}(p, \cdot)$;
- it stores the result in $\mathrm{doms}[b]$.

Here $\mathrm{intersect}(b_1, b_2)$ moves two fingers up the array, repeatedly replacing the finger with the smaller postorder number $f$ by $\mathrm{doms}[f]$, until they meet, and returns the common node.

1. **Correctness.** The algorithm terminates, and then $\mathrm{doms}[b]$ is the immediate dominator of $b$ for every $b \ne n_0$. For every node $b$, $\mathrm{Dom}(b)$ is the set of nodes on the path $b, \mathrm{doms}[b], \mathrm{doms}[\mathrm{doms}[b]], \dots, n_0$, which is the path from $n_0$ to $b$ in the dominator tree.
2. **Cost.** Each pass takes time $O(N + E \cdot D)$, where $N$ and $E$ are the numbers of nodes and edges and $D$ is the length of the longest chain $b, \mathrm{doms}[b], \dots, n_0$ that the intersections of that pass traverse; $D \le N$. Once the algorithm has converged these chains are the final dominator sets, but on an earlier pass a provisional chain can be longer than every final dominator set.

**Proof idea.** In reverse postorder of a depth-first search the parent of each node in the [search tree comes earlier](../../../graph-algorithms/traversal-and-connectivity/depth-first-search/parent-before-child-decreasing-finish.md), so on the first pass every node other than $n_0$ has a predecessor whose entry is already defined. The array represents each set $D(b)$ of the [iterative dataflow solution](dominator-sets-as-a-dataflow-problem.md) as the chain from $b$ to $n_0$, in the order of the path in the dominator tree. Nodes higher in that tree have larger postorder numbers, so walking the finger with the smaller number up the chain computes the intersection of two such sets. Each pass therefore performs one pass of the iterative dataflow algorithm.

## Depends on

- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)
- [Dominator sets as a dataflow problem](dominator-sets-as-a-dataflow-problem.md)

## Proof depends on

- [In decreasing finish order, a DFS parent precedes its child](../../../graph-algorithms/traversal-and-connectivity/depth-first-search/parent-before-child-decreasing-finish.md)

## Sources

- L. Georgiadis, R. E. Tarjan and R. F. Werneck, "Finding dominators in practice", *Journal of Graph Algorithms and Applications* 10(1):69–94, 2006, doi:10.7155/jgaa.00119, Section 2.1, pp. 72–74: the data-flow equations and their iterative solution; the tree-based iteration attributed to Cooper, Harvey and Kennedy, which represents every set $\mathrm{Dom}'(v)$ as the ancestors of $v$ in one tree rooted at $r$, replaces the parent of $v$ by the nearest common ancestor of its processed predecessors, and stops with the dominator tree; processing in reverse postorder of a depth-first search starting from the tree $\{r\}$ (their implementation IDFS); and the cost of computing nearest common ancestors by ascending the tree paths until they meet, $O(mn)$ per iteration. The finger rule on postorder numbers and the refinement of the per-pass bound to $O(N + E \cdot D)$, with $D$ the longest chain traversed, are written out here.
- K. D. Cooper, T. J. Harvey and K. Kennedy, *A Simple, Fast Dominance Algorithm*, Rice University Computer Science Technical Report TR-06-33870: section "Engineering the Data Structures" (the $\mathrm{doms}$ array and the two-finger intersection on postorder numbers), Figure 3, and section "Complexity Analysis".

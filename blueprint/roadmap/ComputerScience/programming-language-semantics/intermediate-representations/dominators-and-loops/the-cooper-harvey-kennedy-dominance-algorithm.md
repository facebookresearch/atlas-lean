# The Cooper–Harvey–Kennedy dominance algorithm

Let $G$ be a finite control-flow graph with entry node $n_0$ in which every node is reachable from $n_0$, and number its nodes in postorder of a depth-first search from $n_0$, so that $n_0$ has the largest number. The algorithm keeps an array $\mathrm{doms}$, initially undefined except $\mathrm{doms}[n_0] = n_0$, and repeats passes until a pass changes nothing. In each pass it visits the nodes $b \ne n_0$ in reverse postorder:
- it starts from one predecessor of $b$ whose entry is already defined;
- it combines it with every other predecessor $p$ whose entry is defined, by $\mathrm{intersect}(p, \cdot)$;
- it stores the result in $\mathrm{doms}[b]$.

Here $\mathrm{intersect}(b_1, b_2)$ moves two fingers up the array, repeatedly replacing the finger with the smaller postorder number $f$ by $\mathrm{doms}[f]$, until they meet, and returns the common node.

1. **Correctness.** The algorithm terminates, and then $\mathrm{doms}[b]$ is the immediate dominator of $b$ for every $b \ne n_0$. For every node $b$, $\mathrm{Dom}(b)$ is the set of nodes on the path $b, \mathrm{doms}[b], \mathrm{doms}[\mathrm{doms}[b]], \dots, n_0$, which is the path from $n_0$ to $b$ in the dominator tree.
2. **Cost.** Each pass takes time $O(N + E \cdot D)$, where $N$ and $E$ are the numbers of nodes and edges and $D$ is the size of the largest dominator set.

**Proof idea.** The array represents each set $D(b)$ of the [iterative dataflow solution](dominator-sets-as-a-dataflow-problem.md) as the chain from $b$ to $n_0$, in the order of the path in the dominator tree. Nodes higher in that tree have larger postorder numbers, so walking the finger with the smaller number up the chain computes the intersection of two such sets. Each pass therefore performs one pass of the iterative dataflow algorithm.

## Depends on

- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)
- [Dominator sets as a dataflow problem](dominator-sets-as-a-dataflow-problem.md)

## Sources

- K. D. Cooper, T. J. Harvey and K. Kennedy, *A Simple, Fast Dominance Algorithm*, Rice University Computer Science Technical Report TR-06-33870:
    - section "Engineering the Data Structures": $\mathrm{Dom}(b) = \{b\} \cup \mathrm{IDom}(b) \cup \mathrm{IDom}(\mathrm{IDom}(b)) \cdots \{n_0\}$, the path in the dominator tree; the $\mathrm{doms}$ array; and the two-finger intersection on postorder numbers;
    - Figure 3 (the engineered algorithm) and Figure 4 (an example);
    - section "Complexity Analysis": the cost $O(N + E \cdot D)$ per iteration.

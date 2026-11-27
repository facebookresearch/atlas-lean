# Triplet precedence digraph and the height integer program

Let $\tau$ be a set of rooted triplets on leaf set $L(\tau)$. The **triplet precedence digraph** $G_\tau$ has vertex set $\binom{L(\tau)}{2}$ and, for each $ij|k \in \tau$, the arcs $ij \to ik$ and $ij \to jk$. If $\tau$ is consistent with a tree $T$, then $G_\tau$ is acyclic, since a directed cycle would give $h_T(x_1, x_2) < h_T(x_2, x_3) < \dots < h_T(x_1, x_2)$. When $G_\tau$ is acyclic with longest path length $\ell$, its **height function** $h_{G_\tau}$ is obtained by giving the sinks the value $\ell + 1$, deleting them, giving the new sinks $\ell$, and so on.

For an integer $s$, the integer program $\mathrm{IP}(\tau, s)$ asks for integer heights $h(i,j) \in \{1, \dots, s\}$, one for each pair $ij \in \binom{L(\tau)}{2}$, that

$$\text{maximize } \sum_{ij} h(i,j) \quad \text{subject to} \quad h(i,k) - h(i,j) \ge 1, \quad h(j,k) - h(i,j) \ge 1 \quad \text{for every } ij|k \in \tau,$$

the constraints being the inequalities that a tree or network height function must satisfy for its consistent triplets.

**Theorem 3.** $G_\tau$ is acyclic if and only if $\mathrm{IP}(\tau, s)$ is feasible for some integer $s$; in that case the minimum feasible $s$ is $\ell + 1$, where $\ell$ is the length of a longest path in $G_\tau$, and $h_{G_\tau}$ is feasible for $\mathrm{IP}(\tau, \ell + 1)$.

**Theorem 4.** If $\tau$ is consistent with a tree, then $h_{G_\tau}$ is the unique optimal solution of $\mathrm{IP}(\tau, \ell + 1)$, that is, the unique feasible height function with values in $\{1, \dots, \ell + 1\}$ of maximum total height.

These results underlie the TripNet heuristic: compute a height function from $\tau$ (first breaking cycles of $G_\tau$ by a feedback-arc heuristic, as minimum feedback arc set is NP-hard), run HBUILD, and if no tree results, split the leaves into SN-sets by deleting maximum-height edges, contract them and recurse, finally adding reticulations to recover the remaining triplets. When $\tau$ is consistent with a tree, TripNet returns a binarization of the BUILD tree.

## Depends on

- [Height functions of rooted trees and networks](height-functions-of-trees-and-networks.md)

## Expansion

The constraints of $\mathrm{IP}(\tau, s)$ say exactly that $h$ strictly increases along every arc of $G_\tau$. A directed cycle makes the system infeasible; conversely, along a longest path of $\ell$ arcs the heights must take $\ell + 1$ distinct values, so $s \ge \ell + 1$, and peeling sinks layer by layer realizes $s = \ell + 1$. The proof of Theorem 3 inducts on $\ell$ by removing the triplets responsible for the arcs into the terminal vertices of longest paths; Theorem 4 follows the same induction, using that for tree-consistent triplets the peeled heights agree with the tree's own heights.

## Sources

- H. Poormohammadi, C. Eslahchi, R. Tusserkani, "TripNet: a method for constructing rooted phylogenetic networks from rooted triplets", PLoS ONE 9(9):e106531 (2014), the definition of $G_\tau$, Definition 4, Theorems 3 and 4 and the TripNet steps (Section 5), <https://doi.org/10.1371/journal.pone.0106531>, PMCID PMC4160195.
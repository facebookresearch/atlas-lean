# Geometric Greedy (Greedy Future)

*Greedy* is the online arborally satisfying algorithm that, at time $t$, adds the minimal set of points on row $t$ needed to satisfy every rectangle with corner $(x_t, t)$ and another corner in the current point set: for every key $a$ such that the rectangle spanned by $(x_t, t)$ and the most recent point $(a, s)$ of column $a$ contains no other point, it adds $(a, t)$. In BST terms this is the offline algorithm Greedy Future (Lucas 1988, Munro 2000), which touches only the search path $\tau_t$ to $x_t$ and rearranges it recursively: if there is a next access ($t < m$) and its key $x_{t+1}$ lies on $\tau_t$, it becomes the root of the rearranged path; if there is a next access and its key is not on $\tau_t$, its predecessor and successor among the keys of $\tau_t$ become the root and the right child of the root (only one of them, as the root, if $x_{t+1}$ lies left of the minimum or right of the maximum of $\tau_t$); the parts of the path not yet placed are then arranged by the same rule applied to the later accesses, and ties, including the case $t = m$ and the parts no later access reaches, are broken arbitrarily. In the geometric form this rule is online.

## Depends on

- [Online arborally satisfying algorithms](online-geometric-algorithm.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
- Joan M. Lucas, "Canonical Forms for Competitive Binary Search Tree Algorithms", Rutgers University Technical Report DCS-TR-250 (1988).
- J. Ian Munro, "On the Competitiveness of Linear Search", ESA (2000).

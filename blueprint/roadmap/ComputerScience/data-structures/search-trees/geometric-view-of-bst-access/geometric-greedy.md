# Geometric Greedy (Greedy Future)

*Greedy* is the online arborally satisfying algorithm that, at time $t$, adds the minimal set of points on row $t$ needed to satisfy every rectangle with corner $(x_t, t)$ and another corner in the current point set: for every key $a$ such that the rectangle spanned by $(x_t, t)$ and the most recent point $(a, s)$ of column $a$ contains no other point, it adds $(a, t)$. In BST terms (Lucas 1988, Munro 2000) Greedy touches the search path to $x_t$ and rearranges it so that the keys to be accessed soonest are nearest the root; in the geometric form this rule is online.

## Depends on

- [Online arborally satisfying algorithms](online-geometric-algorithm.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
- Joan M. Lucas, "Canonical Forms for Competitive Binary Search Tree Algorithms", Rutgers University Technical Report DCS-TR-250 (1988).
- J. Ian Munro, "On the Competitiveness of Linear Search", ESA (2000).

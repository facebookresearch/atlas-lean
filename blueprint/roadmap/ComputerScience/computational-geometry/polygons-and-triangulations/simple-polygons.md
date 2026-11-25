# Simple polygons

A *simple polygon* has a cyclic sequence of $n\ge 3$ pairwise distinct real plane vertices
$v_0,\dots,v_{n-1}$. Its edge $E_i$ is the closed segment $[v_i,v_{i+1}]$, with indices
read modulo $n$. The boundary is simple when both conditions hold:

- $E_i\cap E_{i+1}=\{v_{i+1}\}$ for each $i$, including the last-to-first pair.
- $E_i\cap E_j=\varnothing$ for distinct edges that are not consecutive in either cyclic direction.

Simplicity requires neither an orientation nor strict convexity. For results about the interior,
the polygonal Jordan separation statement is a separate hypothesis: the complement of the boundary
has exactly two connected components, one bounded (the interior) and one unbounded.

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
- J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge University Press, 1998
- D. M. Mount, *CMSC 754 Computational Geometry*, lecture notes, University of Maryland, Fall 2021, Lecture 5 (polygon triangulation)

# Simple polygons

A *simple polygon* with $n \ge 3$ vertices is a cyclic sequence of pairwise distinct points $v_0, \dots, v_{n-1}$ of the plane such that the closed edges $[v_i, v_{i+1}]$ (indices modulo $n$) satisfy: consecutive edges meet only in their shared endpoint, and non-consecutive edges are disjoint. Requiring only consecutive vertices to be distinct gives the same notion: two equal non-adjacent vertices would lie on two non-consecutive edges, which must be disjoint. Results about the interior of a simple polygon take as a hypothesis the Jordan curve theorem for polygons: the complement of the boundary has exactly two connected components, one bounded (the interior) and one unbounded.

## Sources

- M. de Berg, O. Cheong, M. van Kreveld and M. Overmars, *Computational Geometry: Algorithms and Applications*, 3rd ed., Springer, 2008
- J. O'Rourke, *Computational Geometry in C*, 2nd ed., Cambridge University Press, 1998
- D. M. Mount, *CMSC 754 Computational Geometry*, lecture notes, University of Maryland, Fall 2021, Lecture 5 (polygon triangulation)

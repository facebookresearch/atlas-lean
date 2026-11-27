# Configuration space

A *configuration space* is a quadruple $S = (X, \Pi, D, K)$ of a finite *ground set* $X$, a finite set $\Pi$ of *configurations*, and maps $D, K : \Pi \to 2^X$ assigning to each configuration $\Delta$ its set $D(\Delta)$ of *defining elements* and its set $K(\Delta)$ of elements *in conflict* with it, such that $D(\Delta) \cap K(\Delta) = \emptyset$ for all $\Delta$ and only a constant number of configurations share the same defining set. Its *dimension* is $d = \max_{\Delta \in \Pi} |D(\Delta)|$.

For $R \subseteq X$, a configuration $\Delta$ is *active* with respect to $R$ if $D(\Delta) \subseteq R$ and $K(\Delta) \cap R = \emptyset$; the set of active configurations is $T(R)$. For $Q \subseteq X$ and $s \in Q$, $\deg(s, Q)$ is the number of configurations of $T(Q)$ that have $s$ in their defining set. For example, the triangles of the Delaunay triangulation of a point set, with conflicts given by points strictly inside circumcircles, form a configuration space of dimension $3$.

## Related topics

- [Free configuration space](../../not-yet-classified/configuration-space/c-free.md): the configuration space of motion planning, a different notion.

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 8 (The configuration space framework), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%208.pdf>: Definition 8.3 (configuration space, dimension, active configurations $T(R)$), Definition 8.4 ($\deg(s, Q)$) and the Delaunay example after Definition 8.3
- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Linear programming in low dimensions" (Chapter 22), <https://sarielhp.org/book/chapters/lp.pdf>: Definition 22.6.4 (the Clarkson–Shor framework: defining sets of size at most $\delta$ and stopping sets)

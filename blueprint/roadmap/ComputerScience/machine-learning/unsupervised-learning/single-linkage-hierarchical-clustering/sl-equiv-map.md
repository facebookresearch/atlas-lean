# Functoriality of single-linkage clustering

Let $d$ and $e$ be dissimilarities on sets $X$ and $Y$. A distance non-increasing map
$f : (X, d) \to (Y, e)$ (that is, $e(f x, f y) \le d(x, y)$ for all $x, y$) sends
[$r$-equivalent](sl-equiv.md) points to $r$-equivalent points, hence maps each cluster of $X$ into
a cluster of $Y$ at every scale. This is Carlsson's functoriality of clustering (Carlsson,
*Topology and data*, Bull. AMS 2009, Def. 3.2, there for distance-preserving maps) and the
property behind condition (II) of the characterization of single linkage (Carlsson and Mémoli,
JMLR 11 (2010), Thm. 18).

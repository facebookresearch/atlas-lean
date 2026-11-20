# Depth-first search of a Hopcroft–Karp phase

Fix a partner array $\mu$ assigning each right
vertex at most one left partner, and a set $U$ of used left vertices. Write $L_n$ and $R_n$ for
the left and right vertices reached within $n$ rounds of the alternating breadth-first layers of
$\mu$ (so $R_0 = \emptyset$). A left vertex $i$ is unmatched if no right vertex has partner $i$;
otherwise its partner is the least right vertex $j'$ with $\mu(j') = i$. The search from a right
vertex $j$ with bound $n$ and a set $D$ of dead right vertices returns an optional path (a list of
pairs of a left and a right vertex) together with a new dead set:

* if $j \in D$, it fails and returns $D$ unchanged;
* otherwise, if $j \in R_n$, it is the search from $j$ with bound $n - 1$ and dead set $D$;
* otherwise it goes through the candidates, the left vertices $i \in L_n$ in increasing order with
  $j$ adjacent to $i$, $\mu(j) \ne i$ and $i \notin U$. For an unmatched candidate $i$ it returns
  the path $[(i, j)]$ and the current dead set. For a matched candidate $i$ it searches from the
  partner of $i$ with bound $n - 1$ and the current dead set (when $n = 0$ this search fails and
  returns the dead set unchanged); if that search finds a path $P$, it returns $(i, j)$ followed
  by $P$, with the dead set that search returned, and otherwise it moves on to the next candidate
  with the dead set that search returned. If every candidate fails, it fails and returns the
  current dead set with $j$ added.

This is the pruning of Hopcroft and Karp: a right vertex from which the search fails is marked
dead and not searched again.

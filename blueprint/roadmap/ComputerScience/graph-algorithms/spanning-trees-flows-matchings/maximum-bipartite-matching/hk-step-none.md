# A Hopcroft–Karp step that finds nothing

Let $\mu$ be a valid partner array (a matching of
the graph, whose left vertices number $a$). If the Hopcroft–Karp step on $\mu$ returns nothing,
then no right vertex without a partner in $\mu$ is reached within $a + 1$ rounds of the
alternating breadth-first layers of $\mu$.

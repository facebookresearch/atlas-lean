# Termination potential of AC-3

Let $P$ be a binary constraint satisfaction problem with
finitely many variables, $\mathrm{dom}$ finite domains for its variables and $q$ a queue of arcs.
The potential of $\mathrm{dom}$ and $q$ is

$$|q| + \sum_{x} |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x),$$

where $|q|$ is the length of the queue, the sum runs over all variables $x$, and
$\mathrm{indeg}(x)$ is the in-degree of $x$ in $P$.

# A successful Hopcroft–Karp step grows the matching

Let $\mu$ be a valid partner array (a
matching of the graph). If the Hopcroft–Karp step on $\mu$ returns a partner array $\mu'$, then
$\mu'$ is valid and $|\mathrm{matched}(\mu)| + 1 \le |\mathrm{matched}(\mu')|$, where
$\mathrm{matched}(\nu)$ is the set of right vertices that have a partner in $\nu$.

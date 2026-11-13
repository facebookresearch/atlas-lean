# AC-3 revisions are bounded by the potential

For a binary CSP $P$ with finitely many
variables, domains $\mathrm{dom}$ and a queue $q$ of pairs of variables, the number of revisions
AC-3 performs from $\mathrm{dom}$ with queue $q$ is at most the potential
$\ell + \sum_x |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x)$, where $\ell$ is the length of $q$ and
$\mathrm{indeg}(x)$ is the number of entries of the arc list of $P$ ending at $x$.

Each revision lowers the potential by at least $1$.

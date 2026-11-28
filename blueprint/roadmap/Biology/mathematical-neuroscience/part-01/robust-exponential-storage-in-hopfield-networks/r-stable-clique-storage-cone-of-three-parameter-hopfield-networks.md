# r-stable clique storage cone of three-parameter Hopfield networks

**Setting.** Consider the Hopfield network on $n = \binom{2k}{2}$ neurons indexed by the edges of the complete graph on $2k$ vertices, with weights $W_{ef} = x$ when edges $e \ne f$ share one vertex, $W_{ef} = y$ when they are disjoint, and constant threshold $\theta_e = z$ (see [robust exponential storage of cliques](robust-exponential-storage-of-cliques-in-hopfield-networks.md)). For an integer $r \ge 0$, a state $x^*$ is *$r$-stable* if the dynamics converges to $x^*$ from every state within Hamming distance $r$ of $x^*$.

**Lemma.** Fix $k>3$, $0 \le r < k-1$ and $z > 0$. The network stores all $k$-cliques as $r$-stable states if and only if

$$\begin{pmatrix} 4(2-k)+2r & (2-k)(k-3) \\ 4(2-k) & (2-k)(k-3)-2r \end{pmatrix} \begin{pmatrix} x \\ y \end{pmatrix} < \begin{pmatrix} -2 \\ -2 \end{pmatrix} z, \qquad \begin{pmatrix} 2(k-1)+2r & (k-1)(k-2) \\ 2(k-1) & (k-1)(k-2)-2r \end{pmatrix} \begin{pmatrix} x \\ y \end{pmatrix} \le \begin{pmatrix} 2 \\ 2 \end{pmatrix} z$$

componentwise. The last two rows come from edges that must stay off, and an edge is off exactly when its input is at most $z$, so they are non-strict (the source prints all four strict). For $z < 0$ the edges with no clique vertex give a further constraint $\binom{k}{2}y \le z$, which is why $z > 0$ is assumed. Moreover, every pattern within Hamming distance $r$ of a $k$-clique reaches that clique after a single iteration of the dynamics.

## Expansion

Among the patterns within distance $r$ of a fixed $k$-clique, only two extreme corruptions give active constraints; all others yield convex combinations of their inequalities: (i) $r$ clique edges at a common clique vertex are removed, and (ii) $r$ edges are added from one vertex outside the clique to the clique. In case (i), a clique edge $ij$ at the damaged vertex has $2(k-2)-r$ present neighbours and $\binom{k-2}{2}$ present disjoint edges, and must be switched on, which gives $2(2k-r-4)x + (k-2)(k-3)y > 2z$; an edge from another clique vertex to a non-clique vertex has at most $k-1$ present neighbours and $\binom{k-1}{2}-r$ present disjoint edges, and must stay off, which gives $2(k-1)x + ((k-1)(k-2)-2r)y \le 2z$. Case (ii) gives the other two rows in the same way. The solution set is a polyhedral cone in $(x,y,z)$-space; its slice with $y = 0$ (sparse connectivity, each neuron connected only to edges sharing a vertex) and $z=1$ is an interval of admissible $x$, which the paper uses to obtain sparse networks storing every $k$-clique with error-correction radius $r$ of order $k/2$.

## Depends on

- [Robust exponential storage of cliques in Hopfield networks](robust-exponential-storage-of-cliques-in-hopfield-networks.md)

## Sources

- C. J. Hillar, N. M. Tran, "Robust Exponential Memory in Hopfield Networks", Journal of Mathematical Neuroscience (2018), Sect. 5, Exponential Storage (Lemmas 1–2 and their proofs, Eqs. (10)–(12)), <https://doi.org/10.1186/s13408-017-0056-2>, PMCID PMC5770423.

# The next phase's paths are strictly longer

**The next phase's paths are strictly longer** (Hopcroft and Karp). Let $\mu$ be a valid
partner assignment of a bipartite graph (a matching), and let $\mu'$ be obtained from $\mu$ by
flipping all the paths of the phase of $\mu$ at once. If the first free round of $\mu$ is $d$ and
the first free round of $\mu'$ is $d'$, then $d < d'$.

A shortest augmenting path for $\mu'$ of the same length would be a shortest augmenting chain for
$\mu$ that is disjoint from the paths of the phase, contradicting the maximality of the phase.

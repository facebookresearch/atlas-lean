# If generation $n$ is empty, then $F < I_0 + \cdots + I_{n-1}$

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Let $I_m$ be the number
of infectives in [generation $m$](../branching-process-approximation-of-early-epidemi/epi-size.md).
If $I_n = 0$ for some $n$, then the [final size](final-size.md) $F$, the number of individuals ever
infected, satisfies $F < \sum_{m < n} I_m$.

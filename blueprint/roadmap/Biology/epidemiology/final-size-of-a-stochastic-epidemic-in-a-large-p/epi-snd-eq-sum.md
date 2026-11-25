# Contacts made before generation n sum the infectives' contact numbers

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Write $(I_n, D_n)$ for
the [state of the epidemic](../branching-process-approximation-of-early-epidemi/epi.md) at
generation $n$: $I_n$ infectives in generation $n$ and $D_n$ contacts made by generations
$0, \dots, n-1$, with $(I_0, D_0) = (1, 0)$ for the index case. For every $n$, the number of
contacts made by generations $0, \dots, n-1$ is $D_n = \sum_{m < n} \sum_{i < I_m} \xi_{m,i}$.

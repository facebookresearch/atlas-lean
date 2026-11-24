# Total contacts are the sum of the contact numbers of all infectives

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Let $I_n$ be the number
of infectives in [generation $n$](../branching-process-approximation-of-early-epidemi/epi-size.md)
and $\#S_0$ the number of initially susceptible individuals. The
[total number of contacts](total-contacts.md) is $C = \sum_{m=0}^{\#S_0} \sum_{i < I_m} \xi_{m,i}$.

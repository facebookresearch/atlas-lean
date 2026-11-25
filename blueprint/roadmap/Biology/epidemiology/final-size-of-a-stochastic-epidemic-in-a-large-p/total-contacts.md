# Total number of contacts made during the epidemic

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Write $(I_n, D_n)$ for
the [state of the epidemic](../branching-process-approximation-of-early-epidemi/epi.md) at
generation $n$: $I_n$ infectives in generation $n$ and $D_n$ contacts made by generations
$0, \dots, n-1$, with $(I_0, D_0) = (1, 0)$ for the index case. The total number of contacts is
$C = D_{\#S_0+1}$, the number of contacts made by generations $0, \dots, \#S_0$, where $\#S_0$ is
the number of initially susceptible individuals. Generation $\#S_0 + 1$ has no infectives
([extinction by generation $\#S_0 + 1$](../branching-process-approximation-of-early-epidemi/epi-size-card-add-one-eq-zero.md))
and the state stays constant afterwards ([constant state](epi-eq-epi-card-add-one.md)), so $C$
counts every contact of the epidemic.

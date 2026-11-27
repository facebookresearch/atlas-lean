# The final size is the sum of the generation sizes after the index case

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Let $I_n$ be the number
of infectives in [generation $n$](../branching-process-approximation-of-early-epidemi/epi-size.md)
and $\#S_0$ the number of initially susceptible individuals. Then the [final size](final-size.md)
$F$, the number of individuals ever infected, is
$F = \sum_{m=0}^{\#S_0} I_{m+1} = I_1 + I_2 + \cdots + I_{\#S_0+1}$. The later generations are empty
([extinction by generation $\#S_0 + 1$](../branching-process-approximation-of-early-epidemi/epi-size-card-add-one-eq-zero.md)).

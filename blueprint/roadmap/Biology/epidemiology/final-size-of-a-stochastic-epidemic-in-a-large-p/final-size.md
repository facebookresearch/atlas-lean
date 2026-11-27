# Final size: the number of individuals ever infected

Let $\xi_{n,i} \in \mathbb{N}$ be the number of contacts made by the $i$-th infective of generation
$n$, let $U_j$ be the target of contact number $j$ in a population $\alpha$, and let
$S_0 \subseteq \alpha$ be a finite set of initially susceptible individuals. Contact number $j$
[hits](../branching-process-approximation-of-early-epidemi/epi-hit.md) when $U_j \in S_0$ and
$U_{j'} \ne U_j$ for all $j' < j$. The final size is the number of hits among the $C$ contacts of
the epidemic, $C$ being the [total number of contacts](total-contacts.md):
$F = \#\{\, j < C : U_j \in S_0 \text{ and } U_{j'} \ne U_j \text{ for all } j' < j \,\}$. Distinct
hits go to distinct individuals of $S_0$, so $F$ is the number of individuals ever infected; the
index case is not counted.

# Number of hits among the first c contacts

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$
($\#S_0$ of them) and a sequence $v : \mathbb{N} \to \{0, \dots, N-1\}$ of contact targets, the
number of hits among the first $c$ contacts is
$H_c = \#\{\, j < c : v_j \in S_0 \text{ and } v_{j'} \ne v_j \text{ for all } j' < j \,\}$, the
number of contacts $j < c$ that
[hit](../branching-process-approximation-of-early-epidemi/epi-hit.md). The
[final size](final-size.md) is $H_C$, with $C$ the [total number of contacts](total-contacts.md).

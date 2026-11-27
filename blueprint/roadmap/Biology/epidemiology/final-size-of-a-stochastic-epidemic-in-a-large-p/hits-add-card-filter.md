# Hits and never-contacted initial susceptibles together number $\#S_0$

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$
($\#S_0$ of them) and a sequence $v : \mathbb{N} \to \{0, \dots, N-1\}$ of contact targets, and
$c \in \mathbb{N}$, the [number of hits](hits.md) $H_c$ among the first $c$ contacts satisfies
$H_c + \#\{\, a \in S_0 : v_j \ne a \text{ for all } j < c \,\} = \#S_0$: every hit goes to a
distinct individual of $S_0$, and every individual of $S_0$ reached by one of the first $c$ contacts
is hit exactly once.

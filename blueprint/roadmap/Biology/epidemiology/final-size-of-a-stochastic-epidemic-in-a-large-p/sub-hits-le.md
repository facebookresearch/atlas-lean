# Contacts that do not hit go outside $S_0$ or repeat a target

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$
($\#S_0$ of them) and a sequence $v : \mathbb{N} \to \{0, \dots, N-1\}$ of contact targets, and
$c \in \mathbb{N}$, $c - H_c \le O_c + R_c$, where $H_c$ is the [number of hits](hits.md), $O_c$ the
[number of contacts outside $S_0$](outside-contacts.md) and $R_c$ the
[number of repeated contacts](repeat-contacts.md) among the first $c$ contacts. Since $H_c \le c$,
the left side is an ordinary difference.

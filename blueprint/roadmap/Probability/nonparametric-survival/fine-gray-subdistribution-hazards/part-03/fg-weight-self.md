# Fine–Gray weight of a subject at its own observed time

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored).
Let $n \in \mathbb{N}$, let $X_0, \dots, X_{n-1}$ be real observed times, $\varepsilon_0, \dots, \varepsilon_{n-1}$ statuses, and $G : \mathbb{R} \to \mathbb{R}$ any function. The Fine–Gray weight of subject $l$ at the observed time of subject $i$ is $w_l(i) = 1$ if $X_i \le X_l$; $w_l(i) = G(X_i)/G(X_l)$ if $X_i > X_l$ and $\varepsilon_l \notin \{\star, c\}$; and $w_l(i) = 0$ otherwise (see [Fine–Gray censoring weight](../part-04/fg-weight.md)).

For every subject $i$, the weight of $i$ at its own observed time is

$$
w_i(i) = 1.
$$

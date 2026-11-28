# Number of cause-of-interest events in a pair

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set and fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$. The number of cause-$c$ events of a point $x \in S$ is the real number

$$
N(x) = \mathbf{1}[\varepsilon_a(x) = c] + \mathbf{1}[\varepsilon_b(x) = c].
$$

# Cause-of-interest events of the paired design lie in complete pairs

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set, fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$, a sample size $n \in \mathbb{N}$ and a sequence $\omega = (\omega_0, \omega_1, \dots)$ of points of $S$, and put $K = \lfloor n/2 \rfloor$. The paired design of size $n$ has subjects $j = 0, \dots, n-1$ with statuses $\varepsilon_j = \varepsilon_a(\omega_{j/2})$ if $j < 2K$ and $j$ is even, $\varepsilon_j = \varepsilon_b(\omega_{(j-1)/2})$ if $j < 2K$ and $j$ is odd, and $\varepsilon_j = \star$ if $j \ge 2K$.

For every subject $i$ with $\varepsilon_i = c$,

$$
i < 2K.
$$

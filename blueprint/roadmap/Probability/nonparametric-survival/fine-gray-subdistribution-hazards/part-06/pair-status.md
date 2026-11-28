# Statuses of the paired design

Let $\iota$ be a set of causes. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set, fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$, and let $s_j(\omega)$ be the [status sequence of the infinite paired sample](pair-status-seq.md): $\varepsilon_a(\omega_{j/2})$ for even $j$ and $\varepsilon_b(\omega_{(j-1)/2})$ for odd $j$.

For a sample size $n \in \mathbb{N}$, with $K = \lfloor n/2 \rfloor$, and a sequence $\omega$ of points of $S$, the status of subject $j \in \{0, \dots, n-1\}$ is

$$
\varepsilon_j = \begin{cases} s_j(\omega) & \text{if } j < 2K, \\ \star & \text{otherwise}. \end{cases}
$$

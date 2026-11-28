# Status sequence of the infinite paired sample

Let $\iota$ be a set of causes. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set and fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$. For a sequence $\omega = (\omega_0, \omega_1, \dots)$ of points of $S$, the status of subject $j \in \mathbb{N}$ is

$$
s_j(\omega) = \begin{cases} \varepsilon_a(\omega_{j/2}) & \text{if } j \text{ is even}, \\ \varepsilon_b(\omega_{(j-1)/2}) & \text{if } j \text{ is odd}. \end{cases}
$$

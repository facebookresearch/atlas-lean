# Fine–Gray weights in the paired design

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set, fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$, a sample size $n \in \mathbb{N}$ and a sequence $\omega = (\omega_0, \omega_1, \dots)$ of points of $S$, and put $K = \lfloor n/2 \rfloor$. The paired design of size $n$ has subjects $j = 0, \dots, n-1$ with

- observed times $X_j = 1$ if $j < 2K$ and $X_j = 0$ otherwise;
- statuses $\varepsilon_j = \varepsilon_a(\omega_{j/2})$ if $j < 2K$ and $j$ is even, $\varepsilon_j = \varepsilon_b(\omega_{(j-1)/2})$ if $j < 2K$ and $j$ is odd, and $\varepsilon_j = \star$ if $j \ge 2K$.

For a function $G : \mathbb{R} \to \mathbb{R}$, the Fine–Gray weight of subject $l$ at the observed time of subject $i$ is $w_l(i) = 1$ if $X_i \le X_l$; $w_l(i) = G(X_i)/G(X_l)$ if $X_i > X_l$ and $\varepsilon_l \notin \{\star, c\}$; and $w_l(i) = 0$ otherwise (see [Fine–Gray censoring weight](../part-04/fg-weight.md)).

For every function $G$ and every subject $i$ with $\varepsilon_i = c$, the weight of every subject $l$ at the observed time of $i$ is

$$
w_l(i) = \begin{cases} 1 & \text{if } l < 2K, \\ 0 & \text{if } l \ge 2K. \end{cases}
$$

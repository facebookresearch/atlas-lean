# Sums over cause-of-interest events of the paired design as sums over pairs

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set, fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$, a sample size $n \in \mathbb{N}$ and a sequence $\omega = (\omega_0, \omega_1, \dots)$ of points of $S$, and put $K = \lfloor n/2 \rfloor$. The paired design of size $n$ has subjects $j = 0, \dots, n-1$ with statuses $\varepsilon_j = \varepsilon_a(\omega_{j/2})$ if $j < 2K$ and $j$ is even, $\varepsilon_j = \varepsilon_b(\omega_{(j-1)/2})$ if $j < 2K$ and $j$ is odd, and $\varepsilon_j = \star$ if $j \ge 2K$.

For every $n$, every sequence $\omega$ and every function $f : \mathbb{N} \to \mathbb{R}$,

$$
\sum_{0 \le i < n,\ \varepsilon_i = c} f(i) = \sum_{k=0}^{K-1} \Bigl( \mathbf{1}[\varepsilon_a(\omega_k) = c]\, f(2k) + \mathbf{1}[\varepsilon_b(\omega_k) = c]\, f(2k+1) \Bigr).
$$

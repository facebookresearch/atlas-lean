# Normalized Fine–Gray score of the paired design as a rescaled sum over pairs

Let $\iota$ be a set of causes and $c \in \iota$ the cause of interest. A status is either an element of $\iota$ (failure from that cause) or an extra value $\star$ (censored). Let $S$ be a set, fix two status maps $\varepsilon_a, \varepsilon_b$ from $S$ to $\iota \cup \{\star\}$, a sample size $n \in \mathbb{N}$ and a sequence $\omega = (\omega_0, \omega_1, \dots)$ of points of $S$, and put $K = \lfloor n/2 \rfloor$. The paired design of size $n$ has subjects $j = 0, \dots, n-1$ with

- observed times $X_j = 1$ if $j < 2K$ and $X_j = 0$ otherwise;
- covariates $z_j = 1$ if $j < 2K$ and $j$ is even, and $z_j = 0$ otherwise;
- statuses $\varepsilon_j = \varepsilon_a(\omega_{j/2})$ if $j < 2K$ and $j$ is even, $\varepsilon_j = \varepsilon_b(\omega_{(j-1)/2})$ if $j < 2K$ and $j$ is odd, and $\varepsilon_j = \star$ if $j \ge 2K$.

For a function $G : \mathbb{R} \to \mathbb{R}$, the Fine–Gray weight of subject $l$ at the observed time of subject $i$ is $w_l(i) = 1$ if $X_i \le X_l$; $w_l(i) = G(X_i)/G(X_l)$ if $X_i > X_l$ and $\varepsilon_l \notin \{\star, c\}$; and $w_l(i) = 0$ otherwise (see [Fine–Gray censoring weight](../part-04/fg-weight.md)). The Fine–Gray weighted sums are $S_k(b, i) = \sum_{l=0}^{n-1} w_l(i)\, z_l^k e^{b z_l}$ for $k \in \mathbb{N}$ and $b \in \mathbb{R}$ (see [Fine–Gray weighted risk sums](../part-04/fg-weighted-sum.md)). The weighted covariate mean is $\bar z(b, i) = S_1(b, i)/S_0(b, i)$ (see [Fine–Gray weighted covariate mean](../part-03/fg-mean.md)). The Fine–Gray score at $b$ is $U_n(b) = \sum_{0 \le i < n,\ \varepsilon_i = c} \bigl(z_i - \bar z(b, i)\bigr)$ (see [Fine–Gray score](../part-03/fg-score.md)).

With $m(b) = e^b/(e^b + 1)$, the score contribution of a pair $x \in S$ at $b$ is $\psi_b(x) = (1 - m(b))\,\mathbf{1}[\varepsilon_a(x) = c] - m(b)\,\mathbf{1}[\varepsilon_b(x) = c]$ (see [score contribution of a pair](../part-06/pair-score.md)).

For every $\beta_0 \in \mathbb{R}$, every $n$, every sequence $\omega$ and every function $G$,

$$
\frac{U_n(\beta_0)}{\sqrt{n}} = \frac{1}{\sqrt{K}} \Bigl( \sum_{k=0}^{K-1} \psi_{\beta_0}(\omega_k) \Bigr) \sqrt{\frac{K}{n}}.
$$

Real division and inversion use $x/0 = 0$ and $0^{-1} = 0$: for $n = 0$ the left side and $K/n$ are $0$, and for $K = 0$ the factor $1/\sqrt{K}$ is $0$.

# Gate: an infective with at most L infectives up to its generation

For a finite set $S_0$ of initially susceptible individuals of the population $\{0, \dots, N-1\}$
and a [configuration](config.md) $w = (w_1, w_2)$, let $I_n$ be the number of infectives in
generation $n$ of the [epidemic of $w$](epi-of.md). For $L \in \mathbb{N}$ and an index $(n, i)$,
the gate is the real number $G_L(w; n, i) = 1$ if $I_0 + \cdots + I_n \le L$ and $i < I_n$, and
$G_L(w; n, i) = 0$ otherwise. It is $1$ exactly when the $i$-th individual of generation $n$ is an
infective and generations $0, \dots, n$ hold at most $L$ infectives. For fixed targets $w_2$ it
depends only on the offspring numbers $w_1(m, \cdot)$ of the generations $m < n$.

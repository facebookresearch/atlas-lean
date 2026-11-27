# Linear solution of the median-of-medians recurrence

Let $T : \mathbb{N} \to \mathbb{N}$
and $a \in \mathbb{N}$. Suppose that $T(n) \le 20an$ for every $n \le 140$, and that for every
$n > 140$ there are $m, p \in \mathbb{N}$ with $m \le \lfloor (n + 4)/5 \rfloor$,
$p \le \lfloor 7n/10 \rfloor + 6$ and $T(n) \le T(m) + T(p) + an$. Then $T(n) \le 20an$ for
every $n \in \mathbb{N}$.

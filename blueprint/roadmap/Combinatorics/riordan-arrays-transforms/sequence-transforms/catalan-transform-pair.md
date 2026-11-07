# Barry's Catalan transform and its inverse

Let $a, b \colon \mathbb{N} \to \mathbb{Q}$ be
sequences such that, for every $n \ge 0$,

$$b_n = \sum_{j=0}^{n} \sum_{k=0}^{n} \frac{2k+1}{n+k+1} (-1)^{k-j}
\binom{2n}{n-k} \binom{k}{j} a_j.$$

Then for every $n \ge 1$ both

$$b_n = \sum_{k=0}^{n} \frac{k}{2n-k} \binom{2n-k}{n-k} a_k$$

and

$$b_n = \sum_{k=0}^{n} \frac{k}{n} \binom{2n-k-1}{n-k} a_k$$

hold, and for every $n \ge 0$ both

$$a_n = \sum_{k=0}^{\lfloor n/2 \rfloor} (-1)^k \binom{n-k}{k} b_{n-k}$$

and

$$a_n = \sum_{k=0}^{n} (-1)^{n-k} \binom{k}{n-k} b_k$$

hold.

In the hypothesis, the terms with $j > k$ vanish because $\binom{k}{j} = 0$ there.

## Sources

- Paul Barry, "A Catalan Transform and Related Transformations on Integer Sequences", Journal of Integer Sequences 8 (2005), Article 05.4.5, proposition lines 302--311, <https://cs.uwaterloo.ca/journals/JIS/VOL8/Barry/barry84.tex>.

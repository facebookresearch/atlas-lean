# Collision lower bound for a function on uniform samples

Let $f : M \to D$ where $M$ and $D$ are finite with $|M| \ge 100\,|D|$, let $s = \lceil 2\sqrt{|D|}\rceil + 1$, and let $x_1, \dots, x_s$ be i.i.d. uniform on $M$. Then with probability at least $1/2$ there exist $i, j \in \{1, \dots, s\}$ with $f(x_i) = f(x_j)$ and $x_i \ne x_j$.

## Proof sketch

The values $f(x_i)$ are i.i.d. from the pushforward law, which need not be uniform; the every-law birthday bound gives a value collision with probability at least $1 - e^{-s(s-1)/(2|D|)} \ge 1 - e^{-2} \ge 3/4$. Since $s < |M|/2$, the uniform birthday upper bound shows that the points $x_1, \dots, x_s$ are all distinct except with probability at most $1 - e^{-s(s-1)/|M|} \le 1/5$. A value collision among distinct points is a collision of $f$, so the probability is at least $3/4 - 1/5 > 1/2$.

The following general inequality is derived here and is not stated in the cited source: for all finite $M$, $D$ and every $s$,

$$
\Pr\bigl[\exists i,j:\ f(x_i) = f(x_j),\ x_i \ne x_j\bigr] \ge 1 - e^{-s(s-1)/(2|D|)} - \binom{s}{2}\frac{1}{|M|},
$$

by subtracting from the every-law birthday bound the probability that two samples coincide as points of $M$, at most $\binom{s}{2}/|M|$ by the union bound.

## Proof depends on

- [Birthday lower bounds for every sampling law](birthday-bounds-for-every-law.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023, Section 8.3, Lemma 8.2 and its proof (with Appendix B, Theorem B.1 and Corollary B.2).

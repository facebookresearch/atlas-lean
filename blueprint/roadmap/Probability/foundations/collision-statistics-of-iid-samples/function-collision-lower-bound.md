# Collision lower bound for a function on uniform samples

Let $f : M \to D$ where $M$ and $D$ are finite, and let $x_1, \dots, x_s$ be i.i.d. uniform on $M$. Then

$$
\Pr\bigl[\exists i,j:\ f(x_i) = f(x_j),\ x_i \ne x_j\bigr] \ge 1 - e^{-s(s-1)/(2|D|)} - \binom{s}{2}\frac{1}{|M|}.
$$

In particular, if $|M| \ge 100\,|D|$ and $s = \lceil 2\sqrt{|D|}\rceil + 1$, the probability is at least $1/2$.

## Proof sketch

The values $f(x_i)$ are i.i.d. from the pushforward law, which need not be uniform; the every-law birthday bound gives a value collision with probability at least $1 - e^{-s(s-1)/(2|D|)}$. Subtract the probability that two samples coincide as points of $M$, at most $\binom{s}{2}/|M|$ by the union bound. Numerical evaluation at the stated parameters gives $1/2$.

## Proof depends on

- [Birthday lower bounds for every sampling law](birthday-bounds-for-every-law.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.

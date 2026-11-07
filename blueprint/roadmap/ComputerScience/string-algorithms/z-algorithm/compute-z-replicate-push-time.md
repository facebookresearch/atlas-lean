# Z-algorithm cost on a repeated symbol followed by a distinct one

Let $\alpha$ be a type
with a lawful Boolean equality test and let $a \ne b$ be elements of $\alpha$. For every $n \ge 1$,
the Z-algorithm run on the word $a^n b$ has cost exactly $3n - 1$, where the cost counts one unit
for each visited position $i \ge 1$ and one unit for each symbol comparison. In terms of the
input length $N = n + 1$, this is $3N - 4$.

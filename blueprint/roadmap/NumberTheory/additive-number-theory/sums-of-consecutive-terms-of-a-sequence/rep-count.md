# Interval-sum representation count

For a sequence $a_0, a_1, a_2, \ldots$ of natural
numbers and a natural number $n$, $f_a(n)$ is the number of pairs $(u, v)$ of natural numbers
with $u \le v$ and $a_u + a_{u+1} + \cdots + a_v = n$, and $f_a(n) = 0$ if there are infinitely
many such pairs.

The sequence is indexed from $0$ rather than from $1$ as in the source; this does not change the
count. When the sequence is strictly increasing with positive terms there are only finitely many
such pairs, so $f_a(n)$ is then the true number of representations.

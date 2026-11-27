# Negated-remainder sequence with fuel

For real polynomials $a$, $b$ and a natural
number $n$, this is the list of polynomials defined recursively by: for $n = 0$ it is the
one-entry list $(a)$; for fuel $n + 1$ it is $(a)$ if $b = 0$, and otherwise it is $a$
followed by the list for the pair $b$, $-(a \bmod b)$ with fuel $n$, where $a \bmod b$ is the
remainder of $a$ on division by $b$.

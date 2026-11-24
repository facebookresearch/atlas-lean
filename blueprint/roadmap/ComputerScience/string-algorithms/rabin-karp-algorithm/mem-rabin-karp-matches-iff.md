# Correctness of Rabin–Karp matching

For every base $d$, every modulus $q > 0$, all
lists of natural numbers $P$ (the pattern) and $T$ (the text) and every natural number $s$,
Rabin–Karp matching of $P$ in $T$ with base $d$ and modulus $q$ reports the offset $s$ if and
only if $P$ matches $T$ at $s$, that is, $s \le |T|$ and $P$ is a prefix of the suffix of $T$
that starts at position $s$ (counting from $0$).

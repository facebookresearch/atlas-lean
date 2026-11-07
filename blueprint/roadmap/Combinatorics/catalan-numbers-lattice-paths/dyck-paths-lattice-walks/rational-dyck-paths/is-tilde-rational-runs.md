# The rational Dyck path run condition

Let $r, s \in \mathbb{N}$ and let $R$ be a list of
runs, each a pair (letter, length) with a Boolean letter. For the run at position $i$, let $v_i$
be the length of the run at position $i + 1$ if that run exists and has letter false, and
$v_i = 0$ otherwise. Then $R$ satisfies the rational run condition for $q = r/s$ when every run
of letter true, say of length $p$ at position $i$, has $p \le r$ and $p s \le r v_i$.

Applied to the maximal runs of the block word of a Dyck path, this says that every block of $p$
consecutive $1$-peaks has $p \le r$ and is followed by $v$ consecutive $0$-valleys with
$p s \le r v$, that is, $v \ge \lceil p s / r \rceil$ when $r \ge 1$.

## Sources

- Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal of Integer Sequences 28 (2025), Article 25.3.2, Definition 3.

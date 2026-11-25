# Indexed universal hash family

Let $s$ be a finite set of indices from a type $\iota$,
and let $h$ assign to each index $i \in \iota$ a function $h_i$ from a set $\alpha$ to
$\{0, 1, \dots, m - 1\}$. The family $h$ is universal on $s$ if $m > 0$, $s$ is nonempty,
and for all distinct keys $x \ne y$ in $\alpha$ the number of indices $i \in s$ with
$h_i(x) = h_i(y)$, multiplied by $m$, is at most $|s|$.

Each index is counted separately, even when two indices give the same function; this is the
form in which the classical counting arguments, including the one for the mod-prime family,
are carried out. Nonemptiness is required because there is no uniform random choice from an
empty family.

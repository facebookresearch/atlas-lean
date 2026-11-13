# At most two long jobs per machine

Let $p$ and $M$ be natural numbers with $M < 3p$,
and let $\ell$ be a list of natural numbers (the jobs of one machine) whose sum is at most $M$.
Then the number of entries of $\ell$ that are at least $p$, plus the number of entries that are
at least $p$ and greater than $M - p$, is at most $2$. Here $M - p$ is truncated subtraction,
equal to $0$ when $M < p$. So $\ell$ has at most two entries that are at least $p$, and at most
one if one of them is greater than $M - p$.

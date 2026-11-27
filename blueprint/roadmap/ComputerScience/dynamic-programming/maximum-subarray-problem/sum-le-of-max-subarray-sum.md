# Kadane's algorithm bounds every nonempty run

Let $\alpha$ be a linearly ordered type
with an additive monoid structure in which $b \le c$ implies $b + a \le c + a$. If Kadane's
algorithm returns the value $m$ on a list $L$ over $\alpha$, then every nonempty contiguous run
of $L$ has sum at most $m$.

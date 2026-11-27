# Security reduction for Lamport one-time signatures

Let $f : X \to Y$ be a function on a
finite nonempty set $X$, let $\ell \ge 1$ be the message length, and let $A$ be a one-time forger
whose random coins range over a finite nonempty set $R$. Then the probability that $A$ wins the
one-time forgery game against the Lamport scheme built from $f$ is at most $2\ell$ times the
probability that the inverter built from $A$ wins the one-wayness game for $f$.

This is the reduction behind Katz and Lindell, Theorem 12.16: if $f$ is one-way, then Lamport's
scheme is one-time secure.

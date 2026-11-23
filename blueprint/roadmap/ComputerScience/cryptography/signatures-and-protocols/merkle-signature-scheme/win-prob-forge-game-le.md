# Forgery bound up to the key-mismatch event

Let messages be $\ell$-bit strings with $\ell \ge 1$, and let $N \ge 1$. The probability that a forger
succeeds against the $N$-key stateful Merkle signer is at most $N$ times the success probability of
the Lamport one-time forger built by the reduction, plus the probability of the key-mismatch event.
The factor $N$ is the guess of the forgery's index (Katz and Lindell, Section 12.6). The second term
is the forger's own bad-event probability, not the advantage of a collision finder, so this bound
alone does not give existential unforgeability under collision resistance.

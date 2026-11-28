# Bad-event bound from one-wayness

Let messages be $\ell$-bit strings with $\ell \ge 1$, and let $N \ge 1$. Combining the forgery bound
with the reduction from Lamport forgeries to inverting $f$ (Katz and Lindell, Theorem 12.16), the
probability that a forger succeeds against the $N$-key Merkle signer is at most $2 \ell N$ times the
success probability of the inverter for $f$ that Lamport's reduction builds from the reduction's
forger, plus the probability of the key-mismatch event. The second term is not bounded by a
collision finder's advantage, so this is not existential unforgeability from one-wayness and
collision resistance.

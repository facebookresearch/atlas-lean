# Dolev–Strong authenticated broadcast

For every finite set of processes and every fault bound $t$ (even $t \ge n - 1$), the Dolev–Strong protocol solves authenticated Byzantine broadcast in $t + 1$ rounds: a correct process accepts a value received in round $r$ when it carries $r$ distinct signatures starting with the sender's, relays, with its own signature added, each of the first two distinct values it accepts, and finally decides its accepted value if it accepted exactly one value, and a default otherwise. Hence each correct process sends at most two signed chains along each link over the whole execution, so communication is polynomial. This is the message-restricted rule of Dolev and Strong's Theorem 3; their Theorem 1 relays every accepted value and bounds only the number of rounds.

## Proof sketch

If a correct process accepts $v$ in round $r \le t$ as one of its first two values, it relays $v$ and every correct process accepts it by round $r + 1$. A value accepted in round $t + 1$ carries $t + 1$ signatures, one of them from a correct process, which accepted it earlier and relayed it, so every correct process accepts it too. Hence the first two values accepted by any correct process are accepted by every correct process: either all correct processes accept the same single value, or none accepts any value, or all accept at least two, and in each case they decide alike. Validity follows because no chain starting with a correct sender's signature can carry another value.

## Depends on

- [Authenticated Byzantine broadcast with unforgeable signatures](authenticated-byzantine-broadcast-with-unforgeable-signatures.md)

## Sources

- Danny Dolev and H. Raymond Strong, "Authenticated Algorithms for Byzantine Agreement", SIAM Journal on Computing 12(4), 1983, Theorem 1 and Theorem 3 (the restriction to relaying the first two distinct values).

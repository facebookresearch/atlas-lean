# Dolev–Strong authenticated broadcast

For every finite set of processes and every fault bound $t$ (even $t \ge n - 1$), the Dolev–Strong protocol solves authenticated Byzantine broadcast in $t + 1$ rounds: a correct process accepts a value received in round $r$ when it carries $r$ distinct signatures starting with the sender's, relays each newly accepted value with its own signature, and finally decides the unique accepted value or a default. Each correct process sends at most two signed chains along each link over the whole execution, so communication is polynomial.

## Proof sketch

If a correct process accepts $v$ in round $r \le t$, it relays $v$ and every correct process accepts it in round $r + 1$. A value accepted in round $t + 1$ carries $t + 1$ signatures, one of them from a correct process, which accepted it earlier and relayed it. So all correct processes accept the same set of values; relaying at most two values suffices to detect equivocation.

## Depends on

- [Authenticated Byzantine broadcast with unforgeable signatures](authenticated-byzantine-broadcast-with-unforgeable-signatures.md)

## Sources

- Danny Dolev and H. Raymond Strong, "Authenticated Algorithms for Byzantine Agreement", SIAM Journal on Computing, 1983.

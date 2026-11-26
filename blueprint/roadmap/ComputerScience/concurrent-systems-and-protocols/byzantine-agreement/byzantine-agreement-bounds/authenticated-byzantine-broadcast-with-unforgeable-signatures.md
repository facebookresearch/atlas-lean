# Authenticated Byzantine broadcast with unforgeable signatures

In the *authenticated* synchronous model, messages are chains of signatures; an adversary controlling a set $F$ of faulty processes can sign only on behalf of processes in $F$ (unforgeability), and correct processes' signatures can be relayed but not fabricated. A protocol solves *authenticated broadcast* from a designated sender against $t$ faults in $R$ rounds if all correct processes decide a common value, equal to the sender's input when the sender is correct.

## Depends on

- [Interactive consistency](interactive-consistency.md)
- [Byzantine agreement with signed messages](../../byzantine-generals-problem/byzantine-agreement-with-signed-messages.md)

## Sources

- Danny Dolev and H. Raymond Strong, "Authenticated Algorithms for Byzantine Agreement", SIAM Journal on Computing, 1983.

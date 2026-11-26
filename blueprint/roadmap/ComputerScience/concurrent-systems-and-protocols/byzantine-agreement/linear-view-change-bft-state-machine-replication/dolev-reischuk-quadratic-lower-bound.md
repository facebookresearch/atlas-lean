# Byzantine agreement requires quadratic communication

Every deterministic protocol solving Byzantine agreement (or Byzantine broadcast) among $n$ processes tolerating $f$ Byzantine faults in the synchronous model, even with unforgeable signatures, has executions in which correct processes send $\Omega(n f)$ messages in total, and at least $\Omega(n + f^2)$ signatures; for $f = \Theta(n)$ this is $\Omega(n^2)$.

## Proof sketch

Consider an execution in which a set $B$ of $f/2$ processes is Byzantine and ignores all messages from the first $f/2$ correct-looking processes. If some correct process $p$ receives fewer than $f/2$ messages, the adversary can corrupt all of $p$'s senders and make $p$ behave as if isolated, so $p$ must decide a default value; a second execution in which $p$ is correct but the inputs differ then forces disagreement or violates validity. Counting shows that unless correct processes send $\Omega(n f)$ messages some such $p$ exists.

## Depends on

- [Reaching Byzantine agreement](../solves.md)
- [Fail-stop, omission and Byzantine faults](../../distributed-execution-models/fail-stop-omission-and-byzantine-faults.md)

## Proof depends on

- [No synchronous protocol reaches Byzantine agreement when $2 \le n \le 3m$](../not-solves-of-two-le-card.md)

## Sources

- D. Dolev, R. Reischuk, "Bounds on Information Exchange for Byzantine Agreement", Journal of the ACM 32(1) (1985).

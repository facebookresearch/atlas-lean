# Interval decomposition of working sets

For [working sets](the-working-set-of-a-process.md) of a process and all times $t$ and parameters $0 \le \alpha \le \tau$:

1. $W(t, 2\tau) = W(t, \tau) \cup W(t - \tau, \tau)$, so $\omega(t, 2\tau) \le \omega(t, \tau) + \omega(t - \tau, \tau)$;
2. $W(t + \alpha, \tau) = W(t + \alpha, \alpha) \cup W(t, \tau - \alpha)$;
3. $\omega(t, 0) = 0$, and $\omega(t, \tau)$ is nondecreasing in $\tau$, since $W(t, \tau) \subseteq W(t, \tau')$ for $\tau \le \tau'$.

Statement 2 says that the working set at a slightly later time consists of the pages referenced since $t$ together with a part of the current working set, which is why the current working set predicts the near future.

These identities hold up to the pages referenced exactly at the dividing instant ($t - \tau$ in statement 1, $t$ in statement 2), since the windows are open intervals; when no page is referenced at those instants, or when references occur at integer times and windows are taken as the corresponding sets of integer times, they hold exactly.

## Depends on

- [The working set of a process](the-working-set-of-a-process.md)

## Sources

- P. J. Denning, "The working set model for program behavior", *Communications of the ACM* 11(5), 1968, Section 3, property P1 (equations (3)–(4)) and property P2 (equation (6)).

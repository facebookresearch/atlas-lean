# Binary-value broadcast filters values proposed only by Byzantine processes

Let $n \ge 3t + 1$. In binary-value broadcast, each correct process broadcasts its bit $b$, re-broadcasts a bit after receiving it from $t + 1$ distinct processes (if not already done), and adds a bit to its set $\mathrm{bin\_values}$ after receiving it from $2t + 1$ distinct processes. Then: every bit in a correct process's $\mathrm{bin\_values}$ was broadcast by some correct process; if a bit enters the $\mathrm{bin\_values}$ of one correct process it eventually enters that of all correct processes; and every correct process eventually has a nonempty $\mathrm{bin\_values}$. Each correct process sends $O(n)$ messages per bit, $O(n^2)$ in total.

## Proof sketch

A bit received from $t + 1$ processes was sent by at least one correct process, so Byzantine-only values are never echoed by correct processes and can reach at most $t < 2t + 1$ senders. If a correct process collects $2t + 1$ copies, at least $t + 1$ came from correct processes, which every correct process eventually receives and echoes, so all correct processes eventually collect $2t + 1$ copies. Since correct inputs take only two values, some bit is broadcast by at least $t + 1$ correct processes, giving non-emptiness.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Proof depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Sources

- A. Mostéfaoui, H. Moumen, M. Raynal, "Signature-Free Asynchronous Binary Byzantine Consensus with t < n/3, O(n^2) Messages, and O(1) Expected Time", Journal of the ACM 62(4) (2015); PODC 2014.

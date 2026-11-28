# Binary-value broadcast filters values proposed only by Byzantine processes

Let $n \ge 3t + 1$. In binary-value broadcast, each correct process broadcasts its bit $b$, re-broadcasts a bit after receiving it from $t + 1$ distinct processes (if not already done), and adds a bit to its set $\mathrm{bin\_values}$ after receiving it from $2t + 1$ distinct processes. Then: if at least $t + 1$ correct processes broadcast the same bit, it eventually enters the $\mathrm{bin\_values}$ of every correct process (BV-Obligation); every bit in a correct process's $\mathrm{bin\_values}$ was broadcast by some correct process (BV-Justification); if a bit enters the $\mathrm{bin\_values}$ of one correct process it eventually enters that of all correct processes (BV-Uniformity); and every correct process eventually has a nonempty $\mathrm{bin\_values}$ (BV-Termination). Each correct process sends $O(n)$ messages per bit, $O(n^2)$ in total.

## Proof sketch

If $t + 1$ correct processes broadcast a bit, every correct process receives it from $t + 1$ processes and echoes it, so every correct process receives it from all $n - t \ge 2t + 1$ correct processes, giving obligation. A bit received from $t + 1$ processes was sent by at least one correct process, so Byzantine-only values are never echoed by correct processes and can reach at most $t < 2t + 1$ senders. If a correct process collects $2t + 1$ copies, at least $t + 1$ came from correct processes, which every correct process eventually receives and echoes, so all correct processes eventually collect $2t + 1$ copies. Since correct inputs take only two values and $n - t \ge 2t + 1$, some bit is broadcast by at least $t + 1$ correct processes, and obligation gives non-emptiness.

## Depends on

- [Asynchronous binary Byzantine agreement and common coins](asynchronous-binary-byzantine-agreement.md)

## Sources

- A. Mostéfaoui, H. Moumen, M. Raynal, "Signature-Free Asynchronous Binary Byzantine Consensus with t < n/3, O(n^2) Messages, and O(1) Expected Time", Journal of the ACM 62(4) (2015); PODC 2014, authors' copy HAL hal-00944019v2, Section 3.1 (the four properties BV-Obligation, BV-Justification, BV-Uniformity, BV-Termination) and Section 3.2 (Figure 1 and message cost).

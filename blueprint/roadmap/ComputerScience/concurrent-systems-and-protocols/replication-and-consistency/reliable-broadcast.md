# Reliable broadcast

In an asynchronous system of processes with reliable channels in which processes may crash, *reliable broadcast* is given by two primitives, $\mathrm{R\text{-}broadcast}(m)$ and $\mathrm{R\text{-}deliver}(m)$, where every message carries its sender and a sequence number, so that messages are unique. It satisfies:

- *validity*: if a correct process R-broadcasts $m$, it eventually R-delivers $m$;
- *agreement*: if a correct process R-delivers $m$, then all correct processes eventually R-deliver $m$;
- *uniform integrity*: every process R-delivers each message $m$ at most once, and only if $m$ was previously R-broadcast by its sender.

Reliable broadcast can be implemented by diffusion: a process that receives a message for the first time relays it to all processes and then R-delivers it.

## Sources

- T. D. Chandra and S. Toueg, "Unreliable failure detectors for reliable distributed systems", *Journal of the ACM* 43(2):225–267, 1996, Section 4 and Figure 4

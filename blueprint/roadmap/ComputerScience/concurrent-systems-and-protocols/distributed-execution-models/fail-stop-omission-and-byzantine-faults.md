# Fail-stop, omission and Byzantine faults

In a timed message-passing run, a faulty processor $p_i$ may deviate from its protocol in one of four increasingly destructive ways.

- *Fail-stop:* $p_i$ executes its protocol correctly but may stop at any time, and once stopped it does not restart.
- *Omission:* $p_i$ follows its protocol, but an executed $\mathrm{Send}(m, p_j)$ may fail to place $m$ in the buffer of $p_j$, and a $\mathrm{Receive}(p_i)$ that delivers a set $S$, removing all of $S$ from the buffer, may make $p_i$ take the transition for some, possibly empty, subset $S' \subseteq S$.
- *Authenticated Byzantine:* $p_i$ behaves arbitrarily, but messages can be signed with the name of the sending processor so that no other processor can forge the signature.
- *Byzantine:* $p_i$ behaves arbitrarily and there are no signatures, but the receiver of a message knows its sender.

## Depends on

- [Timed message-passing runs](timed-message-passing-runs.md)

## Sources

- C. Dwork, N. Lynch and L. Stockmeyer, "Consensus in the presence of partial synchrony", *Journal of the ACM* 35(2):288–323, 1988, Section 2.2

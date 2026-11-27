# Weak secrecy in the applied pi calculus

Let $A$ be a closed extended process of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md), $s$ a name occurring free in $A$ (the nonce to protect,
whose restriction the construction places at top level), and $\mathrm{ded}$ an event symbol not occurring in $A$. Form the monitored process
$A_s = \nu s.\ (A \mid c(x).\ \mathbf{if}\ x = s\ \mathbf{then}\ \mathbf{event}\ \mathrm{ded}(s))$ for a public channel $c$. The name $s$ is *(weakly) secret* in $A$ if no reduction sequence of $A_s$
satisfies the [event](events-and-correspondence-properties.md) $\mathrm{ded}(s)$: the adversary can never deduce $s$ and send it back. For a process $\nu s.P$ that restricts $s$ at top level, the secrecy of $s$ means its secrecy in $P$, after renaming bound names of $P$ apart from $s$;
the definition does not cover a name bound under a replication or deeper inside a process. Secrecy is a reachability property; strong secrecy, which
also hides partial information, is an equivalence property.

## Depends on

- [Events and correspondence properties](events-and-correspondence-properties.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 6.2, Example 6.1, Definition 6.2 and the remarks after it (restriction to nonces restricted at top level, and the convention of removing that restriction).

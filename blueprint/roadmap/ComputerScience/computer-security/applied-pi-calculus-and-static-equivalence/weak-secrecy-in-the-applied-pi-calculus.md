# Weak secrecy in the applied pi calculus

Let $A$ be a closed extended process of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md), $s$ a name of $A$, and $\mathrm{ded}$ an event symbol not occurring in $A$. Form the monitored process
$A_s = \nu s.\ (A \mid c(x).\ \mathbf{if}\ x = s\ \mathbf{then}\ \mathbf{event}\ \mathrm{ded}(s))$ for a public channel $c$. The name $s$ is *(weakly) secret* in $A$ if no reduction sequence of $A_s$
satisfies the [event](events-and-correspondence-properties.md) $\mathrm{ded}(s)$: the adversary can never deduce $s$ and send it back. Secrecy is a reachability property; strong secrecy, which
also hides partial information, is an equivalence property.

## Depends on

- [Events and correspondence properties](events-and-correspondence-properties.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 6.2, Example 6.1 and Definition 6.2.

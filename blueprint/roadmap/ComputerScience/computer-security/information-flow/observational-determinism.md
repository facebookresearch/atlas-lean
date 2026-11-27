# Low-security observational determinism

Let configurations $m = \langle M, e\rangle$ of a nondeterministic concurrent language produce event traces $m \Downarrow T$, here the sequences $T = [M_0, M_1, \dots]$ of memory states
of the execution, and let $\approx_\zeta$ relate configurations that a low observer at level $\zeta$ cannot distinguish (see
[security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)). For traces, $T \approx_\zeta T'$ holds if for every memory location $L$
the sequences $T(L) = [M_0(L), M_1(L), \dots]$ and $T'(L)$ of its contents are equal up to stuttering and up to one being a prefix of the other, comparing values by $\approx_\zeta$. A program is
*observationally deterministic* for $\zeta$ if

$$m \approx_\zeta m' \wedge m \Downarrow T \wedge m' \Downarrow T' \implies T \approx_\zeta T'$$

for all initial configurations: every execution looks the same to the low observer, however the scheduler resolves nondeterminism. Unlike possibilistic definitions, the
condition is preserved by refinement of the scheduler. The relation $\approx_\zeta$ on traces is not transitive.

## Depends on

- [Security levels, policies and low equivalence](security-levels-policies-and-low-equivalence.md)

## Sources

- S. Zdancewic and A. C. Myers, "Observational determinism for concurrent program security", *Proceedings of the 16th IEEE Computer Security Foundations Workshop (CSFW 2003)*, pp. 29–43, copy at <https://www.cis.upenn.edu/~stevez/papers/ZM03.pdf>: Section 2.1 (condition (1) and event traces), Section 2.3 (condition (3), low-security observational determinism) and Section 2.4 (the per-location comparison of traces up to stuttering and prefixing, and the example showing it is not transitive).

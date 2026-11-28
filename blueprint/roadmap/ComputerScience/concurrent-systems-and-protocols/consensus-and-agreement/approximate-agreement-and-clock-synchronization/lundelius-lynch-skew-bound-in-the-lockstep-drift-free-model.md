# Lundelius–Lynch skew bound in the lockstep drift-free model

Consider $n$ failure-free processes on a complete network whose drift-free hardware clocks run in lockstep with real time, $H_p(t) = t + c_p$ for arbitrary unknown offsets $c_p$, with message delays in $[d_{\min}, d_{\max}]$ known to the processes. Processes have no access to real time: they read only their own clocks, take steps when a message or an external start signal arrives (and possibly when their clock reaches a chosen value), and there are no rounds whose boundaries are common to all processes. An algorithm synchronizes to within $\gamma$ if every process eventually stops and, from then on, the adjusted local times $L_p = H_p + \mathrm{CORR}_p$ of any two processes differ by at most $\gamma$. The optimal worst-case skew is exactly $\bigl(1 - \frac1n\bigr)(d_{\max} - d_{\min})$: no algorithm synchronizes more closely (Lundelius and Lynch, Theorem 3), and the algorithm in which each process sends its clock reading to all others, estimates each offset from the received reading plus the midpoint delay $(d_{\min} + d_{\max})/2$, and adds the average of its $n$ estimates (its own being $0$) to its correction achieves it (Theorem 7).

## Proof sketch

Shifting process $p$'s clock offset by $\delta$ while changing its incoming and outgoing delays by $\mp \delta$ produces an indistinguishable run; chaining such shifts around all processes accumulates a skew of $(1 - 1/n)(d_{\max} - d_{\min})$ that some pair must incur. Averaging midpoint estimates matches this bound.

## Depends on

- [Timed message-passing runs](../../distributed-execution-models/timed-message-passing-runs.md)

## Sources

- Jennifer Lundelius and Nancy Lynch, "An Upper and Lower Bound for Clock Synchronization", Information and Control 62, 1984, Sections 2–4, Theorems 3 and 7.
- Jennifer Lundelius Welch and Nancy Lynch, "A New Fault-Tolerant Algorithm for Clock Synchronization", Information and Computation, 1988.

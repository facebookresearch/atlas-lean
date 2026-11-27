# Lundelius–Lynch skew bound in the lockstep drift-free model

Consider $n$ processes with drift-free hardware clocks $H_p(t) = t + c_p$ for unknown offsets and message delays in $[d_{\min}, d_{\max}]$, running a deterministic full-information protocol for a fixed number of lockstep rounds and then adjusting their clocks. The optimal worst-case skew after adjustment is exactly $\bigl(1 - \frac1n\bigr)(d_{\max} - d_{\min})$: averaging the offset estimates achieves it, and time-shift indistinguishability shows no protocol does better.

## Proof sketch

Shifting process $p$'s clock offset by $\delta$ while changing its incoming and outgoing delays by $\mp \delta$ produces an indistinguishable run; chaining such shifts around all processes accumulates a skew of $(1 - 1/n)(d_{\max} - d_{\min})$ that some pair must incur. Averaging midpoint estimates matches this bound.

## Depends on

- [Timed message-passing runs](../../distributed-execution-models/timed-message-passing-runs.md)

## Sources

- Jennifer Lundelius and Nancy Lynch, "An Upper and Lower Bound for Clock Synchronization", Information and Control, 1984.
- Jennifer Lundelius Welch and Nancy Lynch, "A New Fault-Tolerant Algorithm for Clock Synchronization", Information and Computation, 1988.

# Agent-independent price schedules give truthful online mechanisms

If each agent faces per-period prices $q^t_i(\theta_{-i}) \ge 0$ independent of its own type, the policy allocating agent $i$ at the earliest period in its window whose price is at most $v_i$ is monotone, its critical value is the minimum price over the window, and with critical payments it is truthful, individually rational and makes no positive transfers. When prices are nondecreasing in time, charging the price at arrival equals the critical payment.

## Proof sketch

Agent-independent prices make the critical value the minimum price in the reported window, which can only increase when the window shrinks.

## Depends on

- [Online mechanism with arrival and departure types](online-mechanism-with-arrival-and-departure-types.md)

## Proof depends on

- [Monotone online policies with critical payments are truthful](monotone-online-policies-with-critical-payments-are-truthful.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.

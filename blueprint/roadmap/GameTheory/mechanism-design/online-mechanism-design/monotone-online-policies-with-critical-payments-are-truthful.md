# Monotone online policies with critical payments are truthful

For every monotone causal online policy, charging each allocated agent its critical value (computed over windows it could have reported) yields a mechanism that is dominant-strategy truthful with respect to misreports satisfying no early arrival and no late departure, individually rational, and makes no positive transfers; unallocated agents pay $0$.

## Proof sketch

The critical value is antitone in the window, so narrowing the window can only increase the price; with the window fixed the problem is single-parameter and the critical-value argument applies.

## Depends on

- [Online mechanism with arrival and departure types](online-mechanism-with-arrival-and-departure-types.md)

## Proof depends on

- [Critical-bid mechanisms are truthful and coincide with Myerson payments](../single-parameter-auctions/critical-bid-mechanisms-are-truthful-and-coincide-with-myerson-payments.md)

## Sources

- David C. Parkes, "Online Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.

# Synchronizer settling budgets

## Observation events and the settling guarantee

- [Invalid observation of a voltage between the logic thresholds](invalid-observation.md)
- [Settling guarantee of a family of synchronizer observations](settling-guarantee.md)
- [Event that one synchronizer observation is invalid](invalid-event.md)
- [Event that the resolution time of one observation exceeds its budget](resolution-exceeds-event.md)

## Within-budget observation

- [Within its budget, an observation is observed as its expected bit](observe-observed-voltage-eq-some-of-le.md)
- [Within its budget, an observation is not invalid](not-invalid-observation-of-le.md)

## Invalid observations and budget expiry

- [An invalid observation has a resolution time beyond its budget](resolution-exceeds-of-invalid-observatio.md)
- [The invalid event lies inside the budget-expiry event](invalid-event-subset-resolution-exceeds.md)
- [An exponential tail bound on budget expiry bounds the invalid event](measure-invalid-event-le-of-tail.md)

## Tail bounds and the finite union bound

- [Union bound on invalid observations with unequal budgets](measure-bi-union-invalid-event-le-sum.md)
- [Capped union bound on any invalid synchronizer observation](any-invalid-measure-le-min-one-sum.md)
- [Capped union bound for equal budgets, $\min(1, N c\, e^{-b/\tau})$](measure-bi-union-invalid-event-le-min-on.md)

## An empty index set and a mid-band voltage

- [With no observations, the invalid event has measure zero](measure-bi-union-invalid-event-eq-zero-o.md)
- [With thresholds $1$ and $2$, the voltage $3/2$ is invalid](invalid-observation-one-two-three-halves.md)

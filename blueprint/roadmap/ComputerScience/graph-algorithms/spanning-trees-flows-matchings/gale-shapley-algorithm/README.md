# Gale–Shapley algorithm

## Preferences

- [Preference order of a ranking](to-order.md)
- [Proposers' preferences from rankings](mprefs.md)
- [Receivers' preference profile from rankings](wprefs.md)

## The algorithm

- [Deferred-acceptance state](state.md)
- [Initial state of deferred acceptance](init.md)
- [Free proposer](free.md)
- [Receiver's holder after a proposal](new-holder.md)
- [A proposal](propose.md)
- [Choosing the next proposer](chooser.md)
- [Running deferred acceptance](run.md)
- [Deferred acceptance](gale-shapley.md)

## The invariant

- [Invariant of deferred acceptance](inv.md)
- [A stable matching has no blocking pair](not-blocking.md)
- [Rejected proposals bound stable partners](le-rank-of-rejected.md)
- [Cases of the receiver's new holder](new-holder-cases.md)

## Termination within `n²` proposals

- [Remaining proposals](remaining.md)
- [A proposal adds one to the proposal count](sum-next-propose.md)
- [Deferred acceptance makes at most n² proposals](sum-next-gale-shapley-le.md)

## The output is a perfect matching

- [When deferred acceptance stops, every proposer is held](held-of-done.md)
- [Every receiver holds someone once every proposer is held](holds-of-held.md)
- [Receiver's partner](partner-w.md)
- [Proposer's partner](partner-m.md)
- [The Gale-Shapley matching](gs-matching.md)

## Stability and optimality

- [A proposer's final partner is his last proposal](exists-rank-gs-matching.md)
- [The Gale-Shapley matching is stable](is-stable-gs-matching.md)
- [Proposer-optimality](gs-matching-proposer-optimal.md)
- [Receiver-pessimality](gs-matching-receiver-pessimal.md)

## Strict total orders as rankings

- [Rank under a strict total order](order-rank.md)
- [Every strict total order on $\{0, \dots, n-1\}$ is given by a ranking](exists-to-order-eq.md)
- [Gale-Shapley serves every preference profile with $n$ proposers and $n$ receivers](exists-rankings-gs-matching.md)

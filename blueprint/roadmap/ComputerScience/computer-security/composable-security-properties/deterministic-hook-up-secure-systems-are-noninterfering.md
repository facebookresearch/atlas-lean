# Deterministic hook-up secure systems satisfy Goguen–Meseguer noninterference

A [rated event system](rated-event-systems-and-level-views.md) $RES$ has the *Goguen–Meseguer property* if its traces are deterministic and for every level $l$ and every $t \in T$
there is $t' \in T$ with $t' \upharpoonright \mathit{vue}(l) = t \upharpoonright \mathit{vue}(l)$ and $t' \upharpoonright (I - \mathit{vue}(l)) = \langle\rangle$: deleting the inputs a level cannot see leaves its view
unchanged.

**Theorem.** If $RES$ is hook-up secure, that is, every level view is [restrictive](restrictive-views.md), and its set of traces is deterministic, then $RES$ has the
Goguen–Meseguer property.

## Depends on

- [Rated event systems and level views](rated-event-systems-and-level-views.md)
- [Restrictive views](restrictive-views.md)

## Proof depends on

- [Hidden inputs can be stripped under a restrictive view](hidden-inputs-can-be-stripped-under-a-restrictive-view.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Section 9.8, Definition 15 and Theorem 6 (from Corollary 1 of Theorem 1).

# Hook-up security is preserved by composition

A [rated event system](rated-event-systems-and-level-views.md) is *hook-up secure* if the level view $\mathit{vue}(l)$ is a [restrictive view](restrictive-views.md)
for every level $l$.

**Theorem (McCullough).** If $RES$ is the simple rated hook-up of $RES_1$ and $RES_2$ and both components are hook-up secure, then $RES$ is hook-up secure.

## Depends on

- [Rated event systems and level views](rated-event-systems-and-level-views.md)
- [Restrictive views](restrictive-views.md)

## Proof depends on

- [The hook-up theorem for restrictive views](hook-up-theorem-for-restrictive-views.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Section 9.8, Definition 14 (hook-up security) and Theorem 7 with its proof.

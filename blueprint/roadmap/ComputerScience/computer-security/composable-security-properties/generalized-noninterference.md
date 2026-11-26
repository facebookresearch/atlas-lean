# Generalized noninterference

Let $RES$ be a [rated event system](rated-event-systems-and-level-views.md) whose levels are *unclassified* and *secret*. $RES$ has *generalized noninterference* if for every
legal trace $\tau = \alpha^\frown\beta$ and every sequence $\tau_2 = \alpha^\frown\beta_2$ obtained by inserting or deleting secret inputs in the final part $\beta$, there is a legal trace
$\tau_3 = \alpha^\frown\beta_3$ such that $\beta_3$ differs from $\beta_2$ only in secret outputs. A change of secret inputs can always be repaired by changing later secret outputs,
without touching the unclassified events.

## Depends on

- [Rated event systems and level views](rated-event-systems-and-level-views.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 8, Section 8.4 (generalized noninterference).

# Temperature intervals from heat streams

Let finitely many sensible hot streams (supply above target) and cold streams (target above supply) have positive constant
capacity-flow rates, all temperatures on one scale, and let $\Delta T_{\min} > 0$. Shift the hot temperatures down and the cold ones
up by $\Delta T_{\min}/2$, merge repeated shifted endpoints, sort them, and form the descending intervals between consecutive
endpoints, all of positive width. The surplus of an interval is its width times the sum of the capacity rates of the hot streams
active in it minus that of the active cold streams. Each stream's duty is the sum of its contributions over its active intervals,
so these intervals feed the heat cascade, whose utility targets they determine. A feasible cascade is not a synthesized
exchanger network.

## Depends on

- [Minimum hot utility of a heat cascade](minimum-hot-utility-of-a-heat-cascade.md)

## Proof depends on

## Sources

- *Process Integration*, NPTEL course 103107094, Module 4, Lecture 13, the problem table algorithm with shifted temperatures and the hot and cold utility targets, <https://archive.nptel.ac.in/content/storage2/courses/103107094/module4/lecture4/lecture4.pdf>.

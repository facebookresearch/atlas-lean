# Rated event systems and level views

A *rated event system* $RES = (E, I, O, T, L, \le, \mathit{lvl})$ is an [event system](event-systems-and-their-hook-up.md) $(E, I, O, T)$ with a partially ordered set
$(L, \le)$ of security levels and a map $\mathit{lvl} : E \to L$. A *view* is any subset $v \subseteq E$; two traces look the same to $v$ when their restrictions to $v$ agree.
The *level view* of $l \in L$ is $\mathit{vue}(l) = \{e \in E \mid \mathit{lvl}(e) \le l\}$, the events a user of level $l$ may see. $RES$ is the *simple rated hook-up* of $RES_1$ and
$RES_2$ if their event systems form a simple hook-up, $L_1, L_2 \subseteq L$, and the orders and level maps of the components are the restrictions of $\le$ and $\mathit{lvl}$.
$T$ is *deterministic* if for each $\alpha \in T$ at most one $e \in E - I$ has $\alpha^\frown\langle e\rangle \in T$.

## Depends on

- [Event systems and their hook-up](event-systems-and-their-hook-up.md)

## Sources

- I. Sutherland, T. Korelsky, D. McCullough, D. Rosenthal, J. Seldin, M. Lam, C. Eichenlaub, B. Esrig, J. Hook, C. Kapper, G. Pottinger, O. Rambow and S. Perlo, *Romulus: A Computer Security Properties Modeling Environment, Volume IIa: The Theory of Security*, Technical Report RL-TR-91-36, Rome Laboratory, 1991, copy at <https://archive.org/details/DTIC_ADA236129>: Chapter 9, Sections 9.4–9.6 (Definitions 4–6 and 9–11).

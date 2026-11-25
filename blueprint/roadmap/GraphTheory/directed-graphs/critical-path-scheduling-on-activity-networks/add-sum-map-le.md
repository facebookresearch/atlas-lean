# Critical-path lower bound for feasible schedules

Let $V$ be a set of events and $E$ a set of activities, each activity $e$ an arc from its tail event $t(e)$ to its head event $h(e)$, with duration $\mathrm{dur}(e) \in \mathbb{N}$. Event times $\tau : V \to \mathbb{N}$ form a feasible schedule if $\tau(t(e)) + \mathrm{dur}(e) \le \tau(h(e))$ for every arc $e$. A list of arcs is a walk from $o$ to $d$ if it is empty only when $o = d$, its first arc leaves $o$, the head of each arc is the tail of the next, and its last arc enters $d$. If $\tau$ is a feasible schedule and $l = [e_1, \dots, e_k]$ is a walk from $o$ to $d$, then

$$\tau(o) + \sum_{i=1}^{k} \mathrm{dur}(e_i) \le \tau(d),$$

with repeated arcs counted each time. No finiteness or acyclicity is assumed.

## Sources

- J. E. Kelley Jr. and M. R. Walker, *Critical-path planning and scheduling*, Proceedings of the Eastern Joint Computer Conference, 1959, pp. 160–173.

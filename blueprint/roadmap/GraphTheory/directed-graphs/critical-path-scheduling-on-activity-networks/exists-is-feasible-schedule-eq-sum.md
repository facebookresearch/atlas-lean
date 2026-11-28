# Earliest event dates of an activity-on-arc network

Let $V$ be a set of events and $E$ a set of activities, each activity $e$ an arc from its tail event $t(e)$ to its head event $h(e)$, with duration $\mathrm{dur}(e) \in \mathbb{N}$. Event times $\tau : V \to \mathbb{N}$ form a feasible schedule if $\tau(t(e)) + \mathrm{dur}(e) \le \tau(h(e))$ for every arc $e$. A list of arcs is a walk from $o$ to $d$ if it is empty only when $o = d$, its first arc leaves $o$, the head of each arc is the tail of the next, and its last arc enters $d$. Suppose that $E$ is finite, that the only walk from any event to itself is the empty one, and that every event $v$ is reachable from a source event $s$ by a walk. Then there is a feasible schedule $\tau$ with $\tau(s) = 0$ such that for every event $v$ some walk $[e_1, \dots, e_k]$ from $s$ to $v$ has total duration $\sum_{i=1}^{k} \mathrm{dur}(e_i) = \tau(v)$. No separate finiteness hypothesis on the events is needed: every event other than $s$ is the head of the last arc of a walk from $s$, so there are at most $1 + |E|$ events.

## Sources

- J. E. Kelley Jr. and M. R. Walker, *Critical-path planning and scheduling*, Proceedings of the Eastern Joint Computer Conference, 1959, pp. 160–173.

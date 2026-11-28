# Feasible schedule of an activity-on-arc network

Let $V$ be a set of events and $E$ a set of activities, each activity $e$ an arc from its tail event $t(e)$ to its head event $h(e)$ (parallel arcs stay distinct), with duration $\mathrm{dur}(e) \in \mathbb{N}$. Event times $\tau : V \to \mathbb{N}$ form a feasible schedule if every activity's head event occurs no earlier than its tail event plus its duration:

$$\tau(t(e)) + \mathrm{dur}(e) \le \tau(h(e)) \quad \text{for every } e \in E.$$

All times and durations are natural numbers of ticks.

# Hybrid automata and their executions

A hybrid automaton is $H = (L, n, \mathrm{Init}, \mathrm{Inv}, \mathrm{Flow}, E, \mathrm{Guard}, \mathrm{Reset})$ with a finite set $L$ of
locations, real state $x \in \mathbb{R}^n$, initial set $\mathrm{Init} \subseteq L \times \mathbb{R}^n$, location invariants, flow conditions
(differential equations or inclusions), a finite set $E$ of edges, each with a source location, a target location, a guard and a reset relation
(several edges may join the same pair of locations). A time step of duration
$r \ge 0$ in location $\ell$ follows a solution of the flow condition defined on $[0, r]$ whose values satisfy $\mathrm{Inv}(\ell)$ at every
time, including both endpoints; a jump along an edge from $\ell$ to $\ell'$ requires its guard and applies the reset, and the result must
satisfy $\mathrm{Inv}(\ell')$. An execution alternates time steps and jumps. The timed transition system of $H$ has states
$L \times \mathbb{R}^n$, a transition labelled $r$ for each time step of duration $r$, and a transition labelled $e$ for each
jump along the edge $e$; a pair $(\ell, x)$ is reachable in $H$ exactly when it is reachable in this labelled transition system. Reachability asks whether some finite execution
visits a target state; properties of infinite executions, including Zeno behaviour, are separate notions.

## Sources

- What's Decidable About Hybrid Automata? — T. A. Henzinger, P. W. Kopke, A. Puri, P. Varaiya, UC Berkeley Memorandum UCB/ERL M98/22 (preliminary version STOC 1995). <https://www2.eecs.berkeley.edu/Pubs/TechRpts//1998/ERL-98-22.pdf> Section 2 (rectangular automata: a directed multigraph with vertex labels for initial, invariant and flow conditions and edge labels for pre- and post-conditions and reset variables); this page's invariant, flow, guard and reset sets are arbitrary rather than rectangular.
- Safety Verification of Hybrid Systems Using Barrier Certificates — S. Prajna, A. Jadbabaie, HSCC 2004, Section 3 (hybrid system description). <https://web.mit.edu/~jadbabai/www/papers/hscc04_2.pdf>

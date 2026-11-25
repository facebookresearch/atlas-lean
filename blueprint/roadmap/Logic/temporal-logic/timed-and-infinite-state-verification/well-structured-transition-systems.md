# Well-structured transition systems

A *quasi-ordering* is a reflexive and transitive relation. A quasi-ordering $\le$ on a set $X$ is a *well-quasi-ordering* if every
infinite sequence $x_0, x_1, \dots$ in $X$ has indices $i < j$ with $x_i \le x_j$. A set $I \subseteq X$ is *upward closed* if $x \in I$ and $x \le y$ imply
$y \in I$; ${\uparrow}x = \{y \mid x \le y\}$; and a *basis* of an upward-closed $I$ is a set $I^b$ with $I = \bigcup_{x \in I^b} {\uparrow}x$.

A *transition system* $(S, \to)$ has a set $S$ of states and a relation $\to \subseteq S \times S$; $\mathrm{Pred}(s)$ is the set of immediate
predecessors of $s$, $\to^*$ is the reflexive transitive closure, and the system is *finitely branching* if each state has
finitely many successors. A *well-structured transition system* is a transition system $(S, \to, \le)$ with a
quasi-ordering $\le$ on $S$ such that

1. $\le$ is a well-quasi-ordering, and
2. $\le$ is upward compatible with $\to$: for all $s_1 \le t_1$ and every transition $s_1 \to s_2$ there is $t_2$ with $t_1 \to^* t_2$ and $s_2 \le t_2$.

It has *strong compatibility* if in 2 one can always take $t_1 \to t_2$ in exactly one step. The *covering problem* asks, given states $s$
and $t$, whether some state $t' \ge t$ is reachable from $s$. Finite branching is not part of the definition; results that need it, such as termination by a finite reachability tree, assume it separately.

## Sources

- A. Finkel and Ph. Schnoebelen, "Well-structured transition systems everywhere!", *Theoretical Computer Science* 256(1–2):63–92, 2001: Definition 2.1, the definitions of upward-closed sets and bases in Section 2.1, Section 2.2, Definition 2.5, Definition 4.4 and the statement of the covering problem in Section 3.

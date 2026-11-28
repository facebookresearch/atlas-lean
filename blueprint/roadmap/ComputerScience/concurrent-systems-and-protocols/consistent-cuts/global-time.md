# Global time of a set of events

For a set $X$ of positions of an execution of a set $P$
of processes, the global time $t_X \in \mathbb{N}^P$ is the componentwise maximum of the vector
timestamps $C(e)$ that the vector clock algorithm assigns to the events $e \in X$, and the zero
vector if $X$ is empty.

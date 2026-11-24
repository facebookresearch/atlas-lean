# Load of a machine

Let $I$ be a finite set of tasks with weights $w_i \in \mathbb{R}$ and $A : I \to \{1, \dots, m\}$ an
assignment of the tasks to $m$ identical machines of speed $1$. The load of machine $j$ is the total weight

$$\ell_j(A) = \sum_{i \in I :\ A(i) = j} w_i$$

of the tasks placed on it (Vöcking, *Algorithmic Game Theory*, Chapter 20, Section 20.1).

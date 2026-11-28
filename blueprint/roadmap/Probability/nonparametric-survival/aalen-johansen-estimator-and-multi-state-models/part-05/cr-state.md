# Competing-risks state path of a subject with delayed entry

Let $k$, $n$ and $r$ be natural numbers. Delayed-entry survival data on $k$ grid times and $n$ subjects consist of strictly increasing grid times $t_0 < \dots < t_{k-1}$ and, for each subject $i$, an entry index $\epsilon_i$ (either a grid index or $\bot$, below every grid index), an exit grid index $x_i$, an event flag $\delta_i \in \{\text{true}, \text{false}\}$, with $\epsilon_i < x_i$. Let $\mathrm{cause} : \{0, \dots, n-1\} \to \{0, \dots, r-1\}$ assign a cause to each subject.

The competing-risks state path takes values in $\{\star\} \sqcup \{0, \dots, r-1\}$, where $\star$ is the transient state and a cause $c$ is the absorbing state "failed from cause $c$". For a subject $i$ and a path index $m \in \{0, 1, \dots, k\}$, it is

$$s_i(m) = \begin{cases} \mathrm{cause}(i) & \text{if } x_i + 1 \le m \text{ and } \delta_i = \text{true}, \\ \star & \text{otherwise.} \end{cases}$$

Path index $j$ is read as the state just before $t_j$ and path index $j + 1$ as the state at $t_j$.

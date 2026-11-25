# Global Markov property

Let $G$ be an undirected graph on a finite vertex set $V$, and let $p$ be a real weight on configurations $x : V \to \alpha$ with $\alpha$ finite. For $U \subseteq V$ write $p(x_U)$ for the total weight of the configurations that agree with $x$ on $U$. The weight $p$ has the global Markov property with respect to $G$ when, for all vertex sets $A, B, S$ such that $S$ separates $A$ from $B$ in $G$,

$$p(x_{A \cup B \cup S})\, p(x_S) = p(x_{A \cup S})\, p(x_{B \cup S})$$

for every configuration $x$. When $p$ is nonnegative with positive total weight, this says that the variables in $A$ and $B$ are conditionally independent given those in $S$.

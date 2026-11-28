# Local Markov property

For a graph $G$ on a finite set $V$ of variables with values in a finite set, and a real weight $p$ on configurations $x : V \to \alpha$, write $p(x_U)$ for the total weight of the configurations that agree with $x$ on $U \subseteq V$. The weight $p$ has the local Markov property when, for every vertex $v$ with neighbor set $N(v)$ and $B = V \setminus (\{v\} \cup N(v))$,

$$p(x_{\{v\} \cup B \cup N(v)})\, p(x_{N(v)}) = p(x_{\{v\} \cup N(v)})\, p(x_{B \cup N(v)})$$

for every configuration $x$. When $p$ is nonnegative with total weight $1$, this says each variable is conditionally independent of the variables outside its closed neighborhood given its neighbors.

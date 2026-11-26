# Availability of a two-state repairable component

State $0$ is up and state $1$ is down. Let $\lambda\ge 0$ be the failure rate, $\mu\ge 0$ the repair rate, and $p_0\in[0,1]$ the initial probability of being up. The generator is

$$Q=\begin{pmatrix}-\lambda&\lambda\\\mu&-\mu\end{pmatrix}.$$

For $t\ge 0$, the availability $A(t)$ is the up coordinate of the initial row vector $(p_0,1-p_0)$ multiplied by $e^{tQ}$. In particular, $A(0)=p_0$ and $A(t)\in[0,1]$.

If $\lambda+\mu>0$, put $r=\mu/(\lambda+\mu)$. Then

$$A(t)=r+(p_0-r)e^{-(\lambda+\mu)t},\qquad \lim_{t\to\infty}A(t)=r.$$

The formula follows by averaging the up column of the two-state transition matrix over the initial law. That transition matrix retains the initial state with weight $e^{-(\lambda+\mu)t}$ and uses the state probabilities $(r,1-r)$ with the remaining weight. The displayed identity also holds algebraically for negative $t$, where it is not a probability formula.

If both rates vanish, $Q=0$ and $A(t)=p_0$ at every time. If $\lambda=0$ and $p_0=1$, then $A(t)=1$ at every time. If $\mu=0<\lambda$, availability tends to zero.

## Sources

- The availability formula and its boundary cases are derived here from the finite-state continuous-time transition function and the two-state kernel.

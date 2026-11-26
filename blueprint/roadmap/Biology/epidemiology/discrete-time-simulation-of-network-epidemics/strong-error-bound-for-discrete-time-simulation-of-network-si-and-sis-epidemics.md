# Strong error bound for discrete-time simulation of network SI and SIS epidemics

**Model.** On a graph with $n$ nodes, edge set $E$ and maximum degree $k$, the continuous-time **SI epidemic** $X(t) \in \{0,1\}^n$ infects a susceptible node $j$ at rate $n(j,x)$, the number of its infected neighbors (transmission rate $1$ per infected edge); the **SIS epidemic** additionally lets each infected node recover at rate $\mu$. These are simulated exactly by discrete event simulation (DES). The **discrete-time simulation** (DTS) with step $h$ batches all events of a time step: from state $X_i$, each susceptible node $j$ becomes infected with probability $1 - e^{-h\,n(j,X_i)}$ and, for SIS, each infected node recovers with probability $1 - e^{-\mu h}$, independently across nodes (only primary infections within a step). Both are driven by the same exponential edge timers, so they are coupled pathwise, and the global error is $\epsilon_i = X_i - X(ih)$, measured by the $1$-norm (number of nodes in different states).

**Theorem.**

1. (Monotone coupling, SI.) $X(ih) \ge X_i$ componentwise almost surely: the DTS never infects a node that the exact process has not infected.
2. (SI error.) For $h \le 1$ and $T = ih$,

$$\mathbb E|\epsilon_i| \le C_{SI}\,K_{SI}\,h, \qquad C_{SI} = n k^2 e^{k-2}, \qquad K_{SI} = \frac{e^{kT} - 1}{k}.$$

3. (SIS error.) For $h \le 1$ and $T = ih$,

$$\mathbb E|\epsilon_i| \le C_{SIS}\,K_{SIS}\,h, \qquad C_{SIS} = n k\big(k e^{k-2} + \mu\big), \qquad K_{SIS} = \frac{e^{(k+\mu)T} - 1}{k+\mu}.$$

So the batched simulation converges strongly with order $1$ in the step size, trading a controlled loss of accuracy for not having to process events one at a time.

## Expansion

The proof treats the Markov chain as an ODE $\dot x = f(x)$ and the DTS as its Euler scheme, with $f(x,a) = (g(x,a) - x)/h$ built from the DTS update $g$ and the difference operator $D(x',x,a) = (x' - g(x,a))/h$. The local error $d_i = D(X(ih), X((i-1)h), A_i)$ has $\mathbb E|d_i| \le C h$: within one step the exact process can make secondary infections (chains of transmissions), which the DTS misses, and their number is dominated by a negative binomial variable with parameters depending on $k$ and $h$, giving the factor $k e^{k-2}$ per infected node. The map $f$ is Lipschitz in expectation with constant $L = k$ (SI) or $k + \mu$ (SIS), so Euler's method is $0$-stable, $\mathbb E|Y_i - Z_i| \le \frac{e^{LT} - 1}{L}\max_j \mathbb E|D(Y_j,\cdot) - D(Z_j,\cdot)|$, which turns the local bound into the global one.

## Sources

- Aaron Lucas, Benjamin Armbruster, "Speeding Up Network Simulations Using Discrete Time", arXiv (2013). Section 2 (model, Theorem 1A), Section 3 (Theorems 2A and 2B, Lemmas 3A–5), Appendix. <https://doi.org/10.48550/arXiv.1302.5443>

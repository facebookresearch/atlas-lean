# Point samples of the traveling sine wave

For a positive number of cells $N$ and real $c_0, a, v, L, \Delta t$, put $\Delta x = L/N$. The sample of the traveling wave $c(t,x) = c_0 + a \sin\!\left(\frac{2\pi (x - v t)}{L}\right)$ at time level $n \in \mathbb{N}$ and node $j \in \mathbb{Z}/N\mathbb{Z}$ is

$$w_j^n = c\bigl(n\,\Delta t,\ \bar{j}\,\Delta x\bigr),$$

where $\bar{j} \in \{0, \dots, N-1\}$ is the representative of $j$.

Real division by zero is $0$, so for $L = 0$ both $\Delta x$ and the phase are $0$ and every sample equals $c_0$.

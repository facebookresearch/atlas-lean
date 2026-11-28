# McCulloch–Pitts networks with maximal period $2^n$

**Setting.** A McCulloch–Pitts network on $n$ neurons, with no external input, is a map $\Phi:\{0,1\}^n \to \{0,1\}^n$ whose coordinates are linear threshold functions

$$\Phi(x)_i = H\Big(\sum_{j=1}^n w_{ij}x_j - \theta_i\Big), \qquad H(d) = \begin{cases}1 & d \ge 0,\\ 0 & d < 0,\end{cases}$$

with real weights $w_{ij}$ and thresholds $\theta_i$, iterated synchronously. Its *period* is the length of its longest cycle. The period equals $2^n$ exactly when $\Phi$ is a single cyclic permutation of all $2^n$ states, so every trajectory visits every state. Full period is a necessary condition for a network to behave irregularly, the way a pre-seizure brain state does.

**The map $\Phi_n$.** For $x \in \{0,1\}^n$ let $m$ be the largest index such that $(x_1,\dots,x_m)$ alternates ($0101\ldots$ or $1010\ldots$). Then define

$$\Phi_n(x)_i = \begin{cases}\overline{x_m} & 1 \le i \le m,\\ x_i & m < i \le n,\end{cases}$$

where $\overline{x} = 1 - x$. It satisfies:
- antisymmetry, $\Phi_n(\overline x) = \overline{\Phi_n(x)}$;
- $\Phi_1(0) = 1$;
- for $n \ge 2$, $\Phi_n(x_1,\dots,x_{n-1},0) = (1,\dots,1)$ if $(x_1,\dots,x_{n-1},0)$ is the alternating vector ending $\ldots1010$, and $(\Phi_{n-1}(x_1,\dots,x_{n-1}),0)$ otherwise.

**Theorem 1 (full period).** For every $n \ge 1$ the period of $\Phi_n$ is $2^n$. In fact the states $\Phi_n^t(0,\dots,0)$, $0 \le t \le 2^n - 1$, are pairwise distinct, and $\Phi_n^{2^n-1}(0,\dots,0)$ is the alternating vector ending $\ldots0101$.

**Theorem 2 (threshold realizability).** For every $n \ge 1$ there are linear threshold functions $f_{n,1},\dots,f_{n,n}:\{0,1\}^n \to \{0,1\}$ with $\Phi_n = (f_{n,1},\dots,f_{n,n})$. So for every $n$ there is an $n$-neuron McCulloch–Pitts network with period $2^n$. Explicit integer weights come from the recursion $w_{1,1,1} = -1$, $\theta_{1,1} = 0$, and for $n \ge 2$:
- $w_{n,n,j} = 1$ for $j \not\equiv n \pmod 2$, $w_{n,n,j} = -1$ for $j \equiv n \pmod 2$ with $j < n$, $w_{n,n,n} = n-2$, and $\theta_{n,n} = \lfloor n/2\rfloor$;
- $w_{n,n-1,j} = w_{n-1,n-1,j}$ for $j \le n-2$, $w_{n,n-1,n-1} = w_{n-1,n-1,n-1} + 1$, $w_{n,n-1,n} = -1$, and $\theta_{n,n-1} = \theta_{n-1,n-1}$;
- for $i \le n-2$: $w_{n,i,j} = w_{n-1,i,j} + w_{n-2,i,j}$ for $j \le n-2$, $w_{n,i,n-1} = w_{n-1,i,n-1}$, $w_{n,i,n} = -1$, and $\theta_{n,i} = \theta_{n-1,i} + \theta_{n-2,i} - 1$.

**Counts.** Call two networks isomorphic if one becomes the other by permuting the neurons and flipping bits. For $n = 2$ there are exactly $2$ full-period networks. For $n = 3$ there are $48$, in $2$ isomorphism classes of $24$. By computer search, for $n = 4$ there are $9984$, in $56$ classes.

## Proof sketch

Theorem 1 follows by induction from the three properties. Starting at $0\cdots0$, the trajectory of $\Phi_n$ runs through all $2^{n-1}$ states with last bit $0$, copying $\Phi_{n-1}$, until it reaches the alternating vector. It then jumps to $1\cdots1$. Antisymmetry makes the second half retrace the bit-flipped first half through all states with last bit $1$, ending at the alternating vector ending $\ldots0101$, which maps back to $0\cdots0$. For Theorem 2, the defining properties determine the sequence $(\Phi_n)$ completely, so it is enough to check that the threshold functions have the same three properties. The key identities, both proved by induction, are

$$\sum_{j \not\equiv n \ (2)} w_{n,i,j} = \theta_{n,i}, \qquad \sum_{j \equiv n\ (2)} w_{n,i,j} = \theta_{n,i} - 1 .$$

Adding them gives $\sum_j w_{n,i,j} = 2\theta_{n,i} - 1$, so complementing the input $x \mapsto \overline x$ moves the weighted sum from $s$ to $2\theta_{n,i} - 1 - s$. That flips the Heaviside output and gives antisymmetry. On the alternating vector every unit fires. The trajectory is a Gray-code-like ordering of the cube (each step changes a prefix), so the network is an exhaustive but deterministic generator and does not produce genuinely random output.

## Sources

- V. Chvátal and M. Goldsmith, "Can brains generate random numbers?", in *AIP Conference Proceedings*, AIP, 2013, 271–273, <https://doi.org/10.1063/1.4776527>. Preprint version: arXiv:1208.6451 (2012), Section 3 ("The answer": definition of $\Phi_n$, Theorem 1 and Theorem 2 with the recursive weights) and Section 4 (counts for $n = 2, 3, 4$), <https://doi.org/10.48550/arXiv.1208.6451>.

# Nayak–Wu: quantum lower bound for approximate counting

Let a $T$-query bit-oracle algorithm output, on every input $x \in \{0,1\}^N$, an estimate $y$ with $|y - |x|| < \Delta$ with probability at least $1 - \varepsilon$, where $|x|$ is the Hamming weight and $2\varepsilon \le 1$. If $1/2 \le \Delta$ and $4\Delta \le N$, then for every $0 \le t \le N$

$$\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\Big(\sqrt{\frac{N}{\Delta}} + \frac{\sqrt{t(N - t)}}{\Delta}\Big) \le 16\,T,$$

so approximate counting within additive error $\Delta$ needs $\Omega\big(\sqrt{N/\Delta} + \sqrt{t(N-t)}/\Delta\big)$ queries (Nayak and Wu prove this $\Omega$ form, query counts measured on inputs of weight $t$). For $0 < \Delta \le 1/2$ the estimate determines $|x|$ exactly, and then $\big(1 - 2\sqrt{\varepsilon(1-\varepsilon)}\big)\sqrt{(N - a)(a + 1)} \le 2T$ for every $0 \le a < N$.

## Proof sketch

Thresholding the estimate at $(a + b)/2$ distinguishes weight $a$ from weight $b$ whenever $b - a \ge 2\Delta$; take $b - a = \lceil 2\Delta \rceil \le 4\Delta$. The layers $0$ and $\lceil 2\Delta \rceil$ give $\theta\sqrt{N/\Delta} \le 4T$, and two layers $a \le t \le b$ give $\theta\sqrt{t(N-t)}/\Delta \le 8T$, where $\theta = 1 - 2\sqrt{\varepsilon(1-\varepsilon)}$; adding gives the displayed bound with room to spare. For exact counting use adjacent layers.

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Adversary lower bounds for parity, threshold functions and majority](adversary-bounds-for-symmetric-functions.md)

## Sources

- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", STOC 1999, Theorem 1.11 (the $\Omega$ form, proved by the polynomial method).
- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Theorem 5 and its proof: the weight-layer bound behind the explicit constant.

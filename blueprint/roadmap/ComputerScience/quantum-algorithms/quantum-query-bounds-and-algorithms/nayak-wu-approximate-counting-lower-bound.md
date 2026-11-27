# Nayak–Wu: quantum lower bound for approximate counting

Let $N \ge 1$ and $1/2 \le \Delta < N$, and fix an error $\varepsilon < 1/2$. Every bit-oracle quantum query algorithm that, on every input $x \in \{0,1\}^N$, outputs with probability at least $1 - \varepsilon$ a number $y$ with $|y - |x|| < \Delta$, where $|x|$ is the Hamming weight, makes

$$\Omega\Big(\sqrt{N/\Delta} + \sqrt{t(N - t)}/\Delta\Big)$$

queries on inputs with $t$ ones, for every $0 \le t \le N$.

## Proof sketch

Nayak and Wu prove this with the polynomial method: the acceptance probability after thresholding the output is a polynomial approximating a partial symmetric Boolean function that separates weight $t$ from a weight at distance about $2\Delta$, and their degree bound for such polynomials gives the query bound. (Derived, not stated by Nayak and Wu: the adversary bound for symmetric functions gives an explicit form. Thresholding the estimate at $(a + b)/2$ distinguishes weight $a$ from weight $b$ whenever $b - a \ge 2\Delta$; taking $b - a = \lceil 2\Delta \rceil \le 4\Delta$ (using $4\Delta \le N$), the layers $0$ and $\lceil 2\Delta \rceil$ give $\theta\sqrt{N/\Delta} \le 4T$ and two layers $a \le t \le b$ give $\theta\sqrt{t(N-t)}/\Delta \le 8T$, where $\theta = 1 - 2\sqrt{\varepsilon(1-\varepsilon)}$, so $\theta\big(\sqrt{N/\Delta} + \sqrt{t(N-t)}/\Delta\big) \le 16T$ for every $T$-query algorithm when also $4\Delta \le N$. For $0 < \Delta \le 1/2$ the estimate determines $|x|$ exactly, and adjacent layers give $\theta\sqrt{(N - a)(a + 1)} \le 2T$ for every $0 \le a < N$.)

## Depends on

- [Quantum query algorithms with phase and value oracles](../quantum-adversary-methods/quantum-query-algorithms.md)

## Proof depends on

- [Adversary lower bounds for parity, threshold functions and majority](adversary-bounds-for-symmetric-functions.md)

## Sources

- A. Nayak and F. Wu, "The Quantum Query Complexity of Approximating the Median and Related Statistics", Proceedings of the 31st ACM Symposium on Theory of Computing (STOC 1999); arXiv:quant-ph/9804066: Section 1 (problem 4, the $\Delta$-approximate count, with $\Delta$ in $[1/2, n)$) and Theorem 1.11, proved by the polynomial method.
- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002, Theorem 5 and its proof: the weight-layer bound behind the derived explicit form.

# Entropy rate of the Moran process vanishes without mutation

Consider the two-type Moran process with population size $N$, state $i \in \{0,\dots,N\}$ the number of type-$A$ individuals, frequency-dependent fitnesses

$$f_A(i) = \frac{a(i-1) + b(N-i)}{N-1}, \qquad f_B(i) = \frac{ci + d(N-i-1)}{N-1}$$

for a game matrix $\begin{pmatrix} a & b\\ c & d\end{pmatrix}$, and mutation probabilities $\mu_{AB}(i)$, $\mu_{BA}(i)$. The transition probabilities are

$$T_{i\to i+1} = \frac{i f_A(i)(1-\mu_{AB}(i)) + (N-i) f_B(i)\mu_{BA}(N-i)}{i f_A(i) + (N-i) f_B(i)}\cdot\frac{N-i}{N},$$

$$T_{i\to i-1} = \frac{i f_A(i)\mu_{AB}(i) + (N-i) f_B(i)(1-\mu_{BA}(N-i))}{i f_A(i) + (N-i) f_B(i)}\cdot\frac{i}{N},$$

$T_{i\to i} = 1 - T_{i\to i+1} - T_{i\to i-1}$, with $T_{0\to1} = \mu_{AB}$ and $T_{N\to N-1} = \mu_{BA}$ so that there is no absorbing state. In the **uniform** regime $\mu_{AB}(i) \equiv \mu_{AB}$, $\mu_{BA}(i) \equiv \mu_{BA}$; in the **boundary** regime mutation acts only at $i = 0$ and $i = N$.

The **entropy rate** of the chain $P$ with stationary distribution $s$ is

$$H(P) = \sum_{i=0}^N s_i\, H(T_i), \qquad H(T_i) = -\sum_j T_{i\to j}\log T_{i\to j}.$$

**Theorem.** Let $\mu_{AB} = \mu$ and $\mu_{BA} = k\mu$ with $k > 0$ and $N$ fixed. In both the uniform and the boundary regime, and for any game matrix,

$$\lim_{\mu\to0} H(P) = 0.$$

Since the Moran chain is tridiagonal, $0 \le H(P) \le \log 3$ always.

## Depends on

- [Fixation probability of the Moran process](../moran-fixation.md)

## Expansion

As $\mu \to 0$ with $\mu_{BA}/\mu_{AB} = k$ fixed, the stationary distribution concentrates on the monomorphic states: $s \to \big(k\rho_A/(k\rho_A + \rho_B), 0, \dots, 0, \rho_B/(k\rho_A + \rho_B)\big)$, where $\rho_A, \rho_B$ are the fixation probabilities of a single $A$ or $B$ mutant. The transition entropies at $i = 0$ and $i = N$ are binary entropies of $\mu$ and $k\mu$, which tend to $0$, and the interior states receive vanishing stationary mass, so the weighted sum vanishes. Without mutation the long-run behavior is fixation, and the inherent randomness disappears. In the neutral uniform regime, by contrast, $H(P)$ approaches $\tfrac32\log 2$ as $N \to \infty$ because states near $N/2$ have transitions close to $(1/4,1/2,1/4)$.

## Sources

- Marc Harper, "The inherent randomness of evolving populations", *Physical Review E* 89 (2014), 032709, <https://doi.org/10.1103/PhysRevE.89.032709>; preprint arXiv:1303.1890, <https://doi.org/10.48550/arXiv.1303.1890>. Numbering of the arXiv version: Section 1.1 (Moran process, mutation regimes), Section 1.3 (entropy rate), Section 2.1 (Theorems 1 and 2) and Section 3.

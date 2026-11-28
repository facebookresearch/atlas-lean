# Erdős problem 958: distance multiplicities $n-1, \dots, 1$

For a finite set $A \subseteq \mathbb{R}^2$, let $D(A)$ be the set of distances $\lvert p - q \rvert$ between distinct points $p, q \in A$, and for $d \in \mathbb{R}$ let the multiplicity $m_A(d)$ be the number of unordered pairs $\{p, q\}$ of distinct points of $A$ with $\lvert p - q \rvert = d$.

Conjecture (one direction of Erdős problem 958, for all large sets): there is $N$ such that every finite set $A \subseteq \mathbb{R}^2$ with $n = |A| \ge N$, for which

$$|D(A)| = n - 1 \quad\text{and}\quad \{m_A(d) : d \in D(A)\} = \{1, 2, \dots, n - 1\},$$

either consists of equally spaced points $a, a + v, \dots, a + (n-1)v$ on a line ($v \ne 0$), or consists of equally spaced points $c + r(\cos(\theta + i\alpha), \sin(\theta + i\alpha))$, $0 \le i < n$, along an arc of a circle ($r > 0$, $\alpha \ne 0$). It is false; the refutation is [Erdős problem 958: multiplicities $n-1, \dots, 1$ do not force equal spacing](staircase-multiplicities-force-equally-s-2.md).

## Sources

- T. F. Bloom, Erdős Problems, Problem #958, https://www.erdosproblems.com/958

# Final-size epidemic model: targets independent of offspring numbers

Let $(\Omega, P)$ be a measure space, $\nu$ a measure on $\mathbb{N}$, $N \in \mathbb{N}$, and let
$\xi_{n,i} : \Omega \to \mathbb{N}$ ($n, i \in \mathbb{N}$) and $U_j : \Omega \to \{0, \dots, N-1\}$
($j \in \mathbb{N}$). They form a final-size epidemic model when

- they satisfy the [early-epidemic hypotheses](../branching-process-approximation-of-early-epidemi/is-early-epidemic.md): the offspring numbers $\xi_{n,i}$ are measurable, mutually independent and each has law $\nu$; the targets $U_j$ are mutually independent and $P(U_j = a) = 1/N$ for every $j$ and every individual $a$;
- every target $U_j$ is measurable;
- the whole array $(\xi_{n,i})_{n,i}$ is independent of the whole sequence $(U_j)_j$.

Independence forces $P$, and hence $\nu$, to be a probability measure, and then $N \ge 1$. The
early-epidemic hypotheses say nothing about the joint law of the offspring numbers and the targets;
without the last condition the law of the final size need not be determined by $\nu$ and $N$.

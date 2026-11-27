# Graph shapes of the fixation probability in each evolutionary scenario of the two-strategy Moran game

**Model.** A population of $N$ individuals of types $A$ and $B$ plays a game with positive pay-off matrix $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$. With $i$ individuals of type $A$ and intensity of selection $w \in [0,1]$ (independent of $N$), fitnesses are

$$
f_i = 1 - w + w\Big[a\tfrac{i-1}{N-1} + b\tfrac{N-i}{N-1}\Big], \qquad g_i = 1 - w + w\Big[c\tfrac{i}{N-1} + d\tfrac{N-i-1}{N-1}\Big].
$$

In the Moran process one individual reproduces with probability proportional to fitness and one dies uniformly at random, so $i \to i+1$ with probability $\alpha_i = \frac{i f_i}{i f_i + (N-i) g_i}\frac{N-i}{N}$ and $i \to i-1$ with probability $\beta_i = \frac{(N-i) g_i}{i f_i + (N-i) g_i}\frac{i}{N}$. Let $\pi_i$ be the probability that $A$ fixes from $i$ individuals, $d_i = \pi_i - \pi_{i-1}$ and $r_i = f_i/g_i$; then $d_{i+1} = r_i^{-1} d_i$ and

$$
\pi_1 = \Big(1 + \sum_{j=1}^{N-1} \prod_{k=1}^{j} r_k^{-1}\Big)^{-1}.
$$

Write $\rho_A = \pi_1$ and $\rho_B = 1 - \pi_{N-1}$ for the fixation probabilities of single mutants; the neutral value is $1/N$.

**Evolutionary scenarios.** Following Taylor et al., the top arrows record *invasion*: $B \overset{\rightarrow}{} A$ means $r_1 > 1$ and $\overset{\ \leftarrow}{}$ means $r_{N-1} < 1$ (the reverse arrows the opposite inequalities). The bottom double arrows record *replacement*: the first is $\Rightarrow$ iff $\rho_A > 1/N$, the second is $\Rightarrow$ iff $\rho_B < 1/N$. Of the $16$ combinations only $8$ occur: the dominance scenarios $B \overset{\rightarrow\rightarrow}{\Rightarrow\Rightarrow} A$, $B \overset{\leftarrow\leftarrow}{\Leftarrow\Leftarrow} A$; the coexistence scenarios $B \overset{\rightarrow\leftarrow}{\Rightarrow\Rightarrow} A$, $B \overset{\rightarrow\leftarrow}{\Leftarrow\Leftarrow} A$, $B \overset{\rightarrow\leftarrow}{\Rightarrow\Leftarrow} A$; and the coordination scenarios $B \overset{\leftarrow\rightarrow}{\Rightarrow\Rightarrow} A$, $B \overset{\leftarrow\rightarrow}{\Leftarrow\Leftarrow} A$, $B \overset{\leftarrow\rightarrow}{\Leftarrow\Rightarrow} A$.

**Theorem (graph shapes).** For $i \in \{1, \dots, N-1\}$:

1. In $B \overset{\leftarrow\leftarrow}{\Leftarrow\Leftarrow} A$, $\pi_i < i/N$ and $d_i$ is increasing (convex graph); in $B \overset{\rightarrow\rightarrow}{\Rightarrow\Rightarrow} A$, $\pi_i > i/N$ and $d_i$ is decreasing (concave graph).
2. If the invasion scenario is $B \overset{\rightarrow\leftarrow}{} A$, there is a unique inflection point $i^*$ with $d_{i+1} < d_i$ for $i < i^*$ and $d_{i+1} > d_i$ for $i > i^*$ (concave then convex). In $B \overset{\rightarrow\leftarrow}{\Rightarrow\Leftarrow} A$ the graph crosses the neutral line exactly once: there is a unique $\bar i \in \{2, \dots, N-2\}$ with $\pi_i \ge i/N$ for $i < \bar i$ and $\pi_i < i/N$ for $i \ge \bar i$; in $B \overset{\rightarrow\leftarrow}{\Rightarrow\Rightarrow} A$ (resp. $\Leftarrow\Leftarrow$) $\pi_i > i/N$ (resp. $< i/N$) throughout.
3. If the invasion scenario is $B \overset{\leftarrow\rightarrow}{} A$, there is a unique inflection point with $d_i$ first increasing then decreasing (convex then concave); in $B \overset{\leftarrow\rightarrow}{\Leftarrow\Rightarrow} A$ the graph crosses the neutral line exactly once, from below to above; in the other two coordination scenarios it stays on one side.

So each evolutionary scenario determines a definite qualitative shape of $i \mapsto \pi_i$.

## Depends on

- [Moran fixation probability](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Expansion

Because $f_i$ and $g_i$ are affine in $i$, the ratio $r_i$ is monotone in $i$. In the dominance scenarios $r_i$ stays on one side of $1$, so $d_{i+1}/d_i = r_i^{-1}$ keeps a fixed side of $1$ and $\pi$ is convex or concave; comparing with the chord $i/N$ gives the sign of $\pi_i - i/N$. In the coexistence (coordination) scenarios $r_i$ decreases (increases) and crosses $1$ once, which produces the unique inflection point. A concave-then-convex (or convex-then-concave) sequence through $(0,0)$ and $(N,1)$ crosses the chord $i/N$ at most once, which gives the single-crossing statements. Frequency-independent fitness ($a = b$, $c = d$) recovers the classical Moran process with constant relative fitness, and $w = 0$ the neutral case $\pi_i = i/N$.

## Sources

- E. P. Souza, E. M. Ferreira, A. G. M. Neves, "Fixation probabilities for the Moran process in evolutionary games with two strategies: graph shapes and large population asymptotics", arXiv:1805.00117 (2018): Section 2 (model, fitnesses, recursion for $d_i$, scenario notation, Theorem 1: the $8$ possible scenarios, with a new proof in the proofs appendix), Section 3 (Propositions 1–4, graph shapes). <https://doi.org/10.48550/arXiv.1805.00117> Published version: Journal of Mathematical Biology 78 (2019) 1033–1065, <https://doi.org/10.1007/s00285-018-1300-4>.

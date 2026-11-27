# Polynomial–exponential dichotomy for discovering a broad peak

**Model.** Sequences of length $L$ over a four-letter alphabet form the sequence space $\{1,2,3,4\}^L$, with Hamming distance $d$. An asexual population of size $N$ with small mutation rate $u$ evolves in the origination–fixation regime: the population is monomorphic, and the probability of moving in one step from sequence $i$ to a sequence $j$ at Hamming distance one is

$$P_{i,j} = \frac{Nu}{3L}\,\rho_{i,j},$$

where $\rho_{i,j}$ is the fixation probability of a single $j$ mutant in an $i$ population. In a flat landscape $\rho_{i,j} = 1/N$ and $P_{i,j} = u/(3L)$, an evolutionary random walk.

**Broad peak landscape.** Fix a target center $s^\ast$ and a width $c \in (0,1)$. The target set is $\{s : d(s, s^\ast) \le cL\}$, which contains at least $2^{cL}/(3L)$ sequences, and the fitness landscape outside it is flat. The discovery time is the hitting time of the target set from a sequence outside it.

**Theorem.** Consider a single search on the broad peak landscape with width $c$ and mutation rate $u$.

1. If $c < 3/4$, there is $L_0 \in \mathbb N$ such that for all $L \ge L_0$ the expected discovery time is at least

$$\exp\!\left[(3 - 4c)\,\frac{L}{16}\,\log\frac{6}{4c + 3}\right].$$

2. If $c \ge 3/4$, then for all $L$ the expected discovery time is at most $O(L^3/u)$.

The lower bound holds for any population size $N$ with $4^L \gg N$, and even when the starting sequence is only a few mutations outside the target set. The threshold $3/4$ is the typical relative distance of a random sequence from $s^\ast$ (three of four letters mismatch): inside that distance neutral drift pushes the walk away from the center, outside it drift pulls it closer. For example, a sequence of length $L = 1000$ with a very broad peak $c = 1/2$ has an expected discovery time of about $10^{65}$ generations, whereas bacterial life has had at most about $10^{14}$ generations.

## Depends on

- [Weak-mutation limit justifies the origination–fixation chain](../../origination-fixation-dynamics/weak-mutation-limit-justifies-the-origination-fi.md)
- [Fixation probability of the Moran process](../../../population-genetics/moran-model/moran-fixation.md)

## Expansion

By symmetry, the distance $i = d(s, s^\ast)$ of the current sequence is itself a Markov chain on $\{0, 1, \dots, L\}$. In the flat landscape it moves from $i$ to $i - 1$ with probability $ui/(3L)$, since one of the $i$ mismatched positions must mutate to the single correct letter, and to $i + 1$ with probability $u(L-i)/L$, since any mutation at a matched position increases the distance; the ratio of outward to inward steps is $3(L-i)/i$, which exceeds $1$ exactly when $i < 3L/4$. The expected hitting time $H(j,i)$ from $i$ to $j < i$ satisfies

$$H(j,i) = 1 + P_{i,i+1}\,H(j,i+1) + P_{i,i-1}\,H(j,i-1) + P_{i,i}\,H(j,i), \qquad j < i < L,$$

with $H(j,j) = 0$, and it can be written as $H(j,i) = \sum_{n=L-i}^{L-j-1} b_n$, where

$$b_0 = \frac{1}{P_{L,L-1}}, \qquad b_n = \frac{1 + P_{L-n,L-n+1}\,b_{n-1}}{P_{L-n,L-n-1}}, \quad n > 0 .$$

If the ratio $P_{L-n,L-n+1}/P_{L-n,L-n-1}$ is at least some $\lambda > 1$, the $b_n$ grow at least geometrically; if it is at most $1$ and $P_{L-n,L-n-1} \ge \alpha > 0$, they grow at most arithmetically with difference $1/\alpha$. For $c < 3/4$ the ratio is at least some $\lambda > 1$ at all distances between $cL$ and $(3 + 4c)L/8$, an interval of length $(3 - 4c)L/8$, so $H(cL, i) \ge \lambda^{(3-4c)L/8}$ for every $i > cL$. For $c \ge 3/4$ the ratio is at most $1$ at every distance above $cL$, which gives the polynomial bound.

## Sources

- K. Chatterjee, A. Pavlogiannis, B. Adlam, M. A. Nowak, "The time scale of evolutionary innovation", PLoS Computational Biology 10(9) (2014) e1003818, Theorem 1, Remark 1, Table 1, and Materials and Methods Eqs. 1–2 (detailed proofs in Text S1, Theorem S2 and Corollary S2), <https://doi.org/10.1371/journal.pcbi.1003818> (PMC4161296).

# Ehrenfeucht-Haussler-Kearns-Valiant lower bound for PAC learning

Let $X$ be a measurable space with measurable singletons and $C$ a class of functions $X \to \{0,1\}$ (not necessarily measurable) that shatters a finite set $W$. Let $\mathcal{D}$ be a family of distributions on $X \times \{0,1\}$ containing every realizable distribution $P \circ (x \mapsto (x, c(x)))^{-1}$ with $P$ a probability measure on $X$ and $c \in C$. If a randomized learner using $m$ examples is an $(\varepsilon, \delta)$-PAC learner for $C$ over $\mathcal{D}$ with $0 < \varepsilon \le 1/8$ and $0 < \delta \le 1/20$, then

$$
m \ge \frac{|W| - 1}{32\,\varepsilon}.
$$

Equivalently $\mathrm{VCdim}(C) \le 32\varepsilon m + 1$ (Ehrenfeucht, Haussler, Kearns and Valiant for $\delta \le 1/100$; Devroye and Lugosi, Theorem 2, giving the stronger lower bound $(|W| - 1)/(24\varepsilon)$ for $\delta \le 1/20$, valid also for randomized learners). In particular, on every such domain, a class that is PAC learnable (realizable or agnostic, deterministic or randomized) has finite VC dimension.

## Proof sketch

Restrict the problem to the shattered set, which preserves PAC learners. Put mass $1 - 8\varepsilon$ on one point $w_0 \in W$ and $8\varepsilon/(|W|-1)$ on each other point. With too few examples, Markov's inequality shows that with probability above $1/2$ the sample reveals at most half of $W \setminus \{w_0\}$. Pairing each of the $2^{|W|-1}$ shattering concepts with its complement on the unseen points (an involution), at least one concept of each pair forces error above $\varepsilon$, so some concept is learned with failure probability exceeding $\delta$ (this argument holds for any $\delta < 1/14$, though the cited sources state $\delta \le 1/20$ and $\delta \le 1/100$).

## Depends on

- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)
- [The realizable distribution family](../../occam-bound-for-consistent-learners/realizable-family.md)
- [Shattering lower bound for PAC learning](../../../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)

## Sources

- A. Ehrenfeucht, D. Haussler, M. Kearns and L. Valiant, "A General Lower Bound on the Number of Examples Needed for Learning", Information and Computation, 1989.
- L. Devroye and G. Lugosi, "Lower bounds in pattern recognition and learning", Pattern Recognition 28(7), 1995, pp. 1011–1018, Section 1 (pp. 1011–1012, restating the Ehrenfeucht–Haussler–Kearns–Valiant bound $(V - 1)/(32\varepsilon)$ for $\varepsilon \le 1/8, \delta \le 1/100$ and noting validity for randomized learners) and Theorem 2 (p. 1013, $(V - 1)/(12\varepsilon)$ for $\delta \le 1/20$ and $\varepsilon < 1/2$).

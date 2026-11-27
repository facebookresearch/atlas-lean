# Comet and Comet-swarm graphs amplify more than the Star

In the generalized Moran process on undirected graphs (see [Fixation probability on the Star graph](fixation-probability-on-the-star-graph.md)), the Star had long been conjectured to be the strongest undirected amplifier. Two families refute this.

**Comet.** For $1 \le m \le N$, the Comet $C^m_N$ consists of a Clique $K_m$ (the *head*) one of whose vertices is the centre of a Star $S_{N-m+1}$ (whose $N - m$ leaves form the *tail*). It interpolates between $C^N_N = K_N$ and $C^1_N = S_N$. For fixed population size there are Comets that amplify more strongly than the Star, for example

$$\rho(1.05, C^{120}_{200}) \ge 0.113 > 0.093 > \rho(1.05, S_{200}).$$

**Comet-swarm.** The Comet-swarm is the [Metastar](fixation-probability-on-the-metastar.md) $\mathcal{M}^{C^{100}_{200}}_{N}$ whose leaves are copies of $C^{100}_{200}$, attached at a tail vertex. Computing $p$, $\alpha$, $\beta$ for $C^{100}_{200}$ exactly and inserting them in the Metastar bound gives, in the limit of large populations,

$$\liminf_{N\to\infty}\rho\big(1.1, \mathcal{M}^{C^{100}_{200}}_N\big) \ge 0.209 > 0.203 > \lim_{N\to\infty}\rho(1.12, S_N) = 1 - 1.12^{-2},$$

and hence, since the Star's limit $1 - r^{-2}$ increases with $r$, the Comet-swarm at fitness $1.1$ beats the Star at every fitness $r' \in [1.1, 1.12]$:

$$\liminf_{N\to\infty}\rho\big(1.1, \mathcal{M}^{C^{100}_{200}}_N\big) \;>\; \lim_{N\to\infty}\rho(r', S_N).$$

In particular, at $r = 1.1$ the Comet-swarm is a stronger amplifier than the Star for all large $N$.

## Depends on

- [Fixation probability on the Star graph](fixation-probability-on-the-star-graph.md)
- [Fixation probability on the Metastar](fixation-probability-on-the-metastar.md)

## Proof sketch

A Comet trades some of the Star's two-step amplification for a well-mixed head that is easy for a mutant to conquer once the head's hub is taken; for weak advantage the balance favours an intermediate tail fraction (the source's Fig. 2 scans $m/N$ at fixed $N$). In a Comet-swarm each leaf graph converts a mutant arrival at its attachment vertex into a whole mutant leaf with probability $\beta$ and a resident arrival into a resident leaf with probability $\alpha$; when $\beta/\alpha$ exceeds the loss from $p < 1$, the Metastar bound $p(1 - r^{-2}\alpha/\beta)$ beats $1 - r^{-2}$. The numerical values are exact computations on the fixed-size Comet, so the large-population comparison at $r = 1.1$ (Counterexample 1 of the source) is rigorous.

## Sources

- A. Pavlogiannis, J. Tkadlec, K. Chatterjee, M. A. Nowak, "Amplification on undirected population structures: Comets beat stars", Scientific Reports (2017), <https://doi.org/10.1038/s41598-017-00107-w> (PMC5427850).

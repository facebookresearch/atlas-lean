# Multi-session hybrid argument for state-separating proofs

Let $\mathrm{real}$ and $\mathrm{ideal}$ be single-session packages with the same interface. For every adversary $\mathcal{A}$ against $m$ parallel sessions there are single-session adversaries $\mathcal{B}_1, \dots, \mathcal{B}_m$, where $\mathcal{B}_j$ runs $\mathcal{A}$ while simulating sessions $i < j$ with $\mathrm{ideal}$ and sessions $i > j$ with $\mathrm{real}$, such that

$$
\mathrm{Adv}\bigl(\mathcal{A}; \mathrm{par}_m(\mathrm{real}), \mathrm{par}_m(\mathrm{ideal})\bigr) \le \sum_{j=1}^m \mathrm{Adv}(\mathcal{B}_j; \mathrm{real}, \mathrm{ideal}).
$$

Each hop replaces exactly one session and equals single-session distinguishing by the corresponding reduction.

## Proof sketch

The $j$-th hybrid package is a reduction package composed with one session; apply the reduction lemma to each hop and the hybrid lemma to the chain.

## Depends on

- [Packages and composition in state-separating proofs](ssp-packages.md)

## Proof depends on

- [Reduction, hybrid and state-simulation lemmas for packages](ssp-reduction-and-hybrid-lemmas.md)

## Sources

- Chris Brzuska et al., "State Separation for Code-Based Game-Playing Proofs", Advances in Cryptology – ASIACRYPT 2018, 2018.

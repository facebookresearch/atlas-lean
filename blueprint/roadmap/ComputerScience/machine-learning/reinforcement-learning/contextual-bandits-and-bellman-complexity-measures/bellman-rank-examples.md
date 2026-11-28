# Bellman rank of tabular and low-rank MDPs

For an episodic MDP with a finite state space $\mathcal{S}$, every value-function class has Bellman rank at most $|\mathcal{S}|$; for an MDP whose transition kernel factorizes as $P(s' \mid s, a) = \langle \phi(s,a), \mu(s')\rangle$ with $d$-dimensional features (a low-rank or linear MDP), the Bellman rank is at most $d$; and for reactive POMDPs with $|\mathcal{S}|$ latent states it is at most $|\mathcal{S}|$.

## Proof sketch

In each case the average Bellman error $\mathcal{E}_h(f', f)$ is an expectation, over the distribution of the latent state (or of the feature vector) at level $h$ under the roll-in policy $\pi_{f'}$, of a quantity depending only on $f$ and the latent state. Writing the expectation as an inner product between the vector of latent-state probabilities (depending on $f'$) and the vector of per-state Bellman errors (depending on $f$) gives a factorization of dimension $|\mathcal{S}|$, or $d$ in the low-rank case.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)
- [Contextual decision processes and Bellman rank](bellman-rank.md)

## Sources

- N. Jiang, A. Krishnamurthy, A. Agarwal, J. Langford, R. E. Schapire, "Contextual Decision Processes with Low Bellman Rank are PAC-Learnable", ICML (2017), arXiv:1610.09512, Propositions 1, 2 and 3 and Appendix B.

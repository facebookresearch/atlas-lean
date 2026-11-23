# Correlated equilibria are coarse correlated equilibria

Summing the correlated $\varepsilon$-equilibrium inequalities of player $i$ over the recommended
strategy $j$ gives the coarse inequality for the fixed deviation $k$, with error
$|S_i|\,\varepsilon$:

$$\mathbb E_\psi[c_i(s)] - \mathbb E_\psi[c_i(k, s_{-i})] = \sum_{j \in S_i} \sum_{s :\, s_i = j} \psi(s)\bigl(c_i(s) - c_i(k, s_{-i})\bigr) \le |S_i|\,\varepsilon .$$

In particular every correlated equilibrium is a coarse correlated equilibrium, that is, lies in
the Hannan set. The two sets coincide when every player has at most two strategies (Hart 2005,
§10.1).

## Background

- [Coarse correlated equilibrium](../no-regret-dynamics/is-coarse-correlated-eq.md): the target
  notion, reached by no-regret (Hannan-consistent) dynamics.

## Sources

- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.1 ("The set of correlated equilibria is contained in the Hannan set").

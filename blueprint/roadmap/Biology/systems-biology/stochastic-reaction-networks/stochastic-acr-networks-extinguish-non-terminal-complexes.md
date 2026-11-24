# Stochastic networks with absolute concentration robustness extinguish non-terminal complexes

Anderson, Enciso and Johnston (2014, Theorem 2) consider a reaction network that is conservative, has deficiency one, and whose deterministic mass action model admits a positive equilibrium for some rate constants, and which has two non-terminal complexes $y_1 \preceq y_2$, meaning that $y_1$ is dominated by $y_2$: $(y_2)_i \le (y_1)_i$ for every species $i$ (the definition just before their Theorem 2). Two complexes that differ in only one species are a special case, since one of them then dominates the other; this is the structural condition of the deterministic absolute concentration robustness theorem, recalled as their Theorem 1. They prove that for any stoichiometrically admissible kinetics, all non-terminal complexes are turned off at each positive recurrent state of the stochastic model; hence a trajectory is absorbed with probability one by a set of states on which all non-terminal complexes are turned off, and in particular the reactions out of $y_1$ and $y_2$ have zero propensity. So the stochastic model of such a network goes extinct where its deterministic model is robust, and the robustness reappears in quasi-stationary distributions (Section 4 of the source).

## Depends on

- [Absolute concentration robustness (Shinar–Feinberg)](../../../Biology/systems-biology/chemical-reaction-network-theory/absolute-concentration-robustness-shinar-feinberg.md)

## Expansion

1. The model: the stochastic reaction network as a continuous-time Markov chain on a finite compatibility class, stoichiometrically admissible kinetics, terminal and non-terminal complexes, and positive recurrent states.
2. The structural argument that from any state some sequence of reactions leads to states where all non-terminal complexes are off, proved in the supplementary material of the source.
3. Theorem 2 and the absorption statement.
4. Quasi-stationary distributions of the robust species for the source's examples, as separate statements.

## Sources

- D. F. Anderson, G. A. Enciso and M. D. Johnston, Stochastic analysis of biochemical reaction networks with absolute concentration robustness, J. R. Soc. Interface 11 (2014), 20130943, Theorems 1 and 2. <https://arxiv.org/abs/1310.3761>

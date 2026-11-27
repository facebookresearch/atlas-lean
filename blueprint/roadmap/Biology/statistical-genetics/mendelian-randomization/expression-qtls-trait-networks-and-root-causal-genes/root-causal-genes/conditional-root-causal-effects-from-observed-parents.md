# Conditional root causal effects from observed parents

Let variables $Z = (\tilde X_1, \dots, \tilde X_p, Y)$ follow a structural equation model $Z_i = f_i(\mathrm{Pa}(Z_i), E_i)$ with mutually independent error terms $E_i$ and an acyclic causal graph, augmented by an edge $E_i \to Z_i$ for each non-root variable; here $\tilde X_i$ are gene expression levels and $Y$ is a disease outcome. The error term $E_i$ is a root cause of $Y$ if it is an ancestor of $Y$ in the augmented graph. Then:

1. if $E_i \not\perp Y$ or $E_i \not\perp Y \mid \mathrm{Pa}(\tilde X_i)$, then $E_i$ is a root cause of $Y$;
2. $P(Y \mid E_i, \mathrm{Pa}(\tilde X_i)) = P(Y \mid \tilde X_i, \mathrm{Pa}(\tilde X_i))$.

Hence the conditional root causal effect

$$\Delta_i = P(Y \mid \mathrm{Pa}(\tilde X_i), E_i) - P(Y \mid \mathrm{Pa}(\tilde X_i)) = P(Y \mid \mathrm{Pa}(\tilde X_i), \tilde X_i) - P(Y \mid \mathrm{Pa}(\tilde X_i))$$

is computable from observed variables without the unobserved errors, and $\Delta_i \ne 0$ certifies that gene $i$ carries a root cause of $Y$. Its expectation version $\Gamma_i = E(Y \mid \mathrm{Pa}(\tilde X_i), \tilde X_i) - E(Y \mid \mathrm{Pa}(\tilde X_i))$, with root causal strength $\Phi_i = |\Gamma_i|$ per sample, ranks root causal genes for each patient.

## Depends on

- [Markovian structural causal model](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/structural-causal-models-and-counterfactuals/scm.md)

## Expansion

By the global Markov property, if $E_i$ is not an ancestor of $Y$ it is d-separated from $Y$ both marginally and given $\mathrm{Pa}(\tilde X_i)$ (the parents are non-descendants of $E_i$), which gives statement 1 by contraposition; the converse needs faithfulness, which is deliberately not assumed. For statement 2, $\tilde X_i$ is a function of $(\mathrm{Pa}(\tilde X_i), E_i)$, and since $\tilde X_i$ is the only child of $E_i$, $E_i$ is d-separated from $Y$ given $\{\tilde X_i\} \cup \mathrm{Pa}(\tilde X_i)$. In practice the parent sets are replaced by surrogate sets found from Perturb-seq knockdowns and the conditional expectations are fitted on bulk RNA-seq, with batch and library-size effects handled so that Poisson measurement error does not bias the estimates.

## Sources

- E. V. Strobl and E. Gamazon, "Discovering root causal genes with high-throughput perturbations", eLife 13 (2025) RP100949, <https://doi.org/10.7554/eLife.100949>, PMCID PMC11882141. Methods: the structural equation model (Equation 3), the root causal effect, Propositions 1–2, and the root causal strength.

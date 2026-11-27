# Extinction of stochastic absolute-concentration-robust networks

**Absolute concentration robustness (ACR).** A deterministic mass-action system has ACR in species $X_i$ if $X_i$ takes the same value at every positive equilibrium. **Shinar–Feinberg theorem:** if a mass-action system admits a positive equilibrium, its network has deficiency $\delta = 1$, and two non-terminal complexes differ only in $X_i$, then the system has ACR in $X_i$.

**Example.** For $A + B \xrightarrow{\alpha} 2B$, $B \xrightarrow{\beta} A$ with total $M = c_A + c_B$, every positive equilibrium has $\bar c_A = \beta/\alpha$ (ACR), and it is stable. In the stochastic model, however, the state $(X_A, X_B) = (M, 0)$ is absorbing and is reached with probability one.

**Definitions.** A complex $y$ is *dominated* by $y'$ ($y \ll y'$) if $y'_i \le y_i$ for every species $i$. A network is *conservative* if some $w \in \mathbb R^m_{>0}$ satisfies $w\cdot(y' - y) = 0$ for every reaction $y \to y'$. Propensities are *stoichiometrically admissible* if a reaction has positive rate exactly when enough reactant molecules are present.

**Theorem (Anderson–Enciso–Johnston).** Consider a conservative network with deficiency one whose deterministic mass-action model admits a positive equilibrium for some rate constants, and suppose two non-terminal complexes satisfy $y_1 \ll y_2$. Then for every choice of stoichiometrically admissible kinetics, all non-terminal complexes are turned off at every positive recurrent state of the stochastic model. Consequently every conservative network guaranteed to be ACR by the Shinar–Feinberg theorem undergoes, in its stochastic version, an **extinction event**: the chain is absorbed in a set of boundary states where the reactions that sustain robustness can no longer fire.

**Timescales.** When absorption is slow relative to the observation window, the relevant object is the quasi-stationary distribution; for the activation/deactivation example the quasi-stationary distribution of $X_A$ converges to a Poisson distribution as $M \to \infty$, recovering the robust deterministic value in the large-copy limit.

## Proof sketch

In the conservative network the chain lives on a finite set, so it is eventually absorbed in a closed communication class. Domination $y_1 \ll y_2$ means that whenever $y_1$ can react, so can $y_2$; combined with the deficiency-one kernel structure this forces any closed class with positive probability flux through non-terminal complexes to be transient. Deterministic ACR and stochastic extinction are therefore two faces of the same structural condition, separated by the large-number limit.

## Sources

- David F. Anderson, Germán A. Enciso and Matthew D. Johnston, "Stochastic analysis of biochemical reaction networks with absolute concentration robustness", *Journal of The Royal Society Interface* 11 (2014), 20130943, <https://doi.org/10.1098/rsif.2013.0943>. Preprint version: arXiv:1310.3761 (2013), Section 2 (activation/deactivation example), Theorems 1–2 (Section 3) and Section 4 (absorption times and quasi-stationary distributions), <https://doi.org/10.48550/arXiv.1310.3761>.

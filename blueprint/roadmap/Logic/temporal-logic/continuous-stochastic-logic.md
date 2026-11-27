# Continuous stochastic logic

This node covers continuous stochastic logic (CSL), a branching-time logic for continuous-time Markov
chains (CTMCs) introduced by Aziz, Sanwal, Singhal and Brayton. Its syntax is that of computation tree
logic together with probability-quantifier formulas $\Pr_{\sim c}(\cdot)$ and time-bounded until
formulas, in the original version multiphase until formulas
$\Phi_0 \, \mathrm{U}^{I_0} \, \Phi_1 \, \mathrm{U}^{I_1} \cdots \mathrm{U}^{I_{K-1}} \, \Phi_K$ with time
intervals $I_k$. Aziz et al. proved that model checking CSL is decidable. Baier, Katoen and Hermanns
gave an approximate model-checking algorithm for the fragment with binary until formulas
$\Phi_1 \, \mathrm{U}^{I} \, \Phi_2$, and Baier, Haverkort, Hermanns and Katoen applied uniformization to its
transient analysis. Time-bounded reachability is
the core computational problem of model checking CSL.

## Background

- [Finite continuous-time Markov chains](../../Probability/markov-chains/finite-continuous-time-markov-chains/README.md)

## Expansion

A sound expansion fixes finite CTMCs with rational rates and their path probability measure, the syntax
of CSL with a stated set of until operators and interval endpoints, and its semantics, and then has
separate pages for: time-bounded reachability probabilities as solutions of a linear differential
system; the correctness of a model-checking procedure for the binary-until fragment with an explicit
treatment of the numerical approximation or of exact comparison with thresholds; and decidability for
multiphase until formulas, with its source. Markov decision processes in continuous time are a
separate node.

## Status

A 2011 note by Jansen corrects a discrepancy between the semantics and the algorithm for the multiple
until operator in the article of Aziz et al.; the expansion must use a statement whose algorithm and
semantics agree.

## Sources

- M. Xu, J. Mei, J. Guan, Y. Deng and N. Yu, "Checking continuous stochastic logic against quantum
  continuous-time Markov chains", Logical Methods in Computer Science 21(4) (2025), §1.1 (the
  history of CSL model checking). <https://arxiv.org/abs/2202.05412>
- M. Salamati, S. Soudjani and R. Majumdar, "A Lyapunov approach for time bounded reachability of
  CTMCs and CTMDPs", preprint version 2 (2020), introduction. <https://arxiv.org/abs/1909.06112>
- D. N. Jansen, "Erratum to: Model-checking continuous-time Markov chains by Aziz et al.", preprint
  (2011), abstract. <https://arxiv.org/abs/1102.2079>

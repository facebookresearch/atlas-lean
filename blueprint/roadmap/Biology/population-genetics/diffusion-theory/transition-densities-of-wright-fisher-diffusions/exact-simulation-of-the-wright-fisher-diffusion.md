# Exact simulation of the Wright–Fisher diffusion

This node covers exact simulation of Wright–Fisher diffusions. Jenkins and Spanò (2017) show that it is
possible to simulate exactly from a broad class of Wright–Fisher diffusions and their bridges: for
reversible neutral diffusions they exploit an eigenfunction expansion of the transition function, which
applies also to the Fleming–Viot process, and for more general drifts, including selection, they develop
an exact rejection algorithm using retrospective simulation. In the neutral case the transition law is a
mixture, over the number of non-mutant ancestral lineages, of binomial-then-Beta draws.

## Expansion

A sound expansion states the line-of-descent mixture representation of the neutral transition law, the
sampling of the number of lineages from its series representation, and then the correctness and almost
sure termination of the neutral algorithm; the rejection algorithm for general drifts is a separate page.

## Sources

- P. A. Jenkins and D. Spanò, "Exact simulation of the Wright–Fisher diffusion", Annals of Applied
  Probability 27 (2017), 1478–1509, <https://doi.org/10.1214/16-AAP1236>.
- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, "Conjugacy properties of time-evolving Dirichlet and gamma random measures", Electronic Journal of Statistics 10 (2016), 3452–3489, <https://doi.org/10.1214/16-EJS1194>, preprint <https://arxiv.org/abs/1607.02896>, Section 2.1.2, equation (11) (the mixture representation of the Wright–Fisher transition function).

# PCTL model checking reduces to reachability

Let $M$ be a finite [Markov decision process](markov-decision-processes-and-adversaries.md) and let $\mathit{Sat}(\phi)$ be the set of states satisfying the [PCTL](pctl.md) formula $\phi$ under all adversaries. Then $\mathit{Sat}$ is computed recursively over the parse tree: $\mathit{Sat}(\neg\phi) = S \setminus \mathit{Sat}(\phi)$, $\mathit{Sat}(\phi_1 \wedge \phi_2) = \mathit{Sat}(\phi_1) \cap \mathit{Sat}(\phi_2)$, $\mathit{Sat}(\mathrm{P}_{\bowtie p}[\psi]) = \{s : \Pr^{\min}_s(\psi) \bowtie p\}$ for lower bounds ${\bowtie} \in \{\ge, >\}$ and $\{s : \Pr^{\max}_s(\psi) \bowtie p\}$ for upper bounds ${\bowtie} \in \{\le, <\}$, where the extremal path probabilities are as follows.

- $\Pr^{\min}_s(\mathrm{X}\,\phi) = \min_{a \in A(s)} \sum_{s' \in \mathit{Sat}(\phi)} \delta(s, a)(s')$, and dually for the maximum.
- $\Pr^{\min}_s(\phi_1\, \mathrm{U}^{\le k}\, \phi_2) = x^k_s$, where $x^\ell_s = 1$ for $s \in \mathit{Sat}(\phi_2)$, $x^\ell_s = 0$ for $s \notin \mathit{Sat}(\phi_1) \cup \mathit{Sat}(\phi_2)$, $x^0_s = 0$ for the remaining states, and $x^\ell_s = \min_{a \in A(s)} \sum_{s'} \delta(s, a)(s')\, x^{\ell - 1}_{s'}$ otherwise; dually for the maximum.
- $\Pr^{\min}_s(\phi_1\, \mathrm{U}\, \phi_2)$ and $\Pr^{\max}_s(\phi_1\, \mathrm{U}\, \phi_2)$ equal the [extremal reachability probabilities](extremal-reachability-probabilities.md) of $\mathit{Sat}(\phi_2)$ in the MDP obtained by making every state outside $\mathit{Sat}(\phi_1)$ absorbing, that is, replacing $\delta(s, a)$ by the point distribution on $s$.

## Depends on

- [PCTL](pctl.md)
- [Extremal reachability probabilities](extremal-reachability-probabilities.md)
- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 6.2.

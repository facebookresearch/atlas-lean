# PCTL

Formulas of *probabilistic computation tree logic* (PCTL) are state formulas $\phi$ and path formulas $\psi$,

$$\phi ::= \mathit{true} \mid c \mid \phi \wedge \phi \mid \neg \phi \mid \mathrm{P}_{\bowtie p}[\psi], \qquad \psi ::= \mathrm{X}\, \phi \mid \phi\, \mathrm{U}^{\le k}\, \phi \mid \phi\, \mathrm{U}\, \phi,$$

where $c$ is an atomic proposition, ${\bowtie} \in \{\le, <, \ge, >\}$, $p \in [0, 1]$ and $k \in \mathbb{N}$. Over a [Markov decision process](markov-decision-processes-and-adversaries.md) $M$ and a class $\mathit{Adv}$ of adversaries, a state $s$ satisfies $\mathit{true}$ always, $c$ if $c \in L(s)$, conjunction and negation as usual, and $\mathrm{P}_{\bowtie p}[\psi]$ if $\Pr^\sigma_{M,s}\{\pi : \pi \models \psi\} \bowtie p$ for every adversary $\sigma \in \mathit{Adv}$. An infinite path $\pi$ satisfies $\mathrm{X}\, \phi$ if $\pi(1) \models \phi$; $\phi_1\, \mathrm{U}^{\le k}\, \phi_2$ if $\pi(i) \models \phi_2$ for some $i \le k$ and $\pi(j) \models \phi_1$ for all $j < i$; and $\phi_1\, \mathrm{U}\, \phi_2$ if it satisfies $\phi_1\, \mathrm{U}^{\le k}\, \phi_2$ for some $k$. The sets of paths satisfying path formulas are measurable. Usually $\mathit{Adv}$ is the set of all adversaries; on a [DTMC](discrete-time-markov-chains.md), the MDP with one action in each state, the semantics needs no adversaries.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)
- [Discrete-time Markov chains](discrete-time-markov-chains.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 6.1, Definitions 12 and 13.

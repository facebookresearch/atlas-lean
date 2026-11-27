# Regular safety properties

A *deterministic finite automaton* (DFA) is a tuple $A = (Q, \bar q, \alpha_A, \delta_A, F)$ of a finite set $Q$ of states, an initial state $\bar q$, a finite alphabet $\alpha_A$, a transition function $\delta_A : Q \times \alpha_A \to Q$ and accepting states $F \subseteq Q$; it is complete if $\delta_A$ is total, and it accepts the finite words $a_0 \dots a_k$ whose run from $\bar q$ ends in $F$. A *regular safety property* $\Phi_P$ over an alphabet $\alpha_P$ is given by an *error automaton* $A^{\mathrm{err}}_P$, a complete DFA over $\alpha_P$ accepting its "bad prefixes":

$$L(\Phi_P) = \{ w \in (\alpha_P)^\omega \mid \text{no prefix of } w \text{ is in } L(A^{\mathrm{err}}_P) \}.$$

For a [Markov decision process](markov-decision-processes-and-adversaries.md) $M$ with $\alpha_P \subseteq \alpha_M$, an adversary $\sigma$ and a state $s$, the probability of satisfying $\Phi_P$ is $\Pr^\sigma_{M,s}(\Phi_P) = \Pr^\sigma_{M,s}\{\pi \mid \mathrm{tr}(\pi){\restriction}_{\alpha_P} \in L(\Phi_P) \cup L^\ast(\Phi_P)\}$, where $\mathrm{tr}(\pi)$ is the action trace of $\pi$, $w{\restriction}_\alpha$ its projection onto $\alpha$, and $L^\ast(\Phi_P)$ the finite words with no prefix in $L(A^{\mathrm{err}}_P)$. A state satisfies the *probabilistic safety property* $P_{\ge p}[\Phi_P]$, for $p \in (0, 1]$, if $\Pr^\sigma_{M,s}(\Phi_P) \ge p$ for all adversaries $\sigma$, that is, if $\Pr^{\min}_{M,s}(\Phi_P) \ge p$.

## Depends on

- [Markov decision processes and adversaries](markov-decision-processes-and-adversaries.md)

## Sources

- V. Forejt, M. Kwiatkowska, G. Norman and D. Parker, "Automated verification techniques for probabilistic systems", *Formal Methods for Eternal Networked Software Systems (SFM 2011)*, LNCS 6659, Springer, 2011, author copy <https://www.prismmodelchecker.org/papers/sfm11.pdf>, Section 7.1, Definitions 14, 15 and 16.

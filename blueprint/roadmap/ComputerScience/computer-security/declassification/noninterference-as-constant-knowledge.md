# Noninterference is constancy of attacker knowledge

A command $c$ of the [language with low events](attacker-knowledge.md) satisfies *noninterference* if whenever $M_1 \sim_\Gamma M_2$ (the memories agree on low
variables), $\langle M_1, c\rangle \xrightarrow{\vec\ell_1}{}^{*} M'_1$ and $\langle M_2, c\rangle \xrightarrow{\vec\ell_2}{}^{*} M'_2$, then $\vec\ell_1 = \vec\ell_2$ (and hence
$M'_1 \sim_\Gamma M'_2$): terminating runs from low-equivalent memories produce the same low events.

**Proposition.** $c$ satisfies noninterference if and only if $k_\downarrow(c, M^0_L, \vec\ell) = k(c, M^0_L)$ for every low projection $M^0_L$ and every
$\vec\ell \in L(c, M^0_L)$: observing a run never refines the attacker's initial knowledge.

## Depends on

- [Attacker knowledge for programs with low events](attacker-knowledge.md)
- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- A. Askarov and A. Sabelfeld, "Gradual release: unifying declassification, encryption and key release policies", *Proceedings of the 2007 IEEE Symposium on Security and Privacy*, copy at <https://www.cs.cornell.edu/~aslan/askarov-sabelfeld-sp07.pdf>: Section 2, Definition 1 (noninterference) and Proposition 2.

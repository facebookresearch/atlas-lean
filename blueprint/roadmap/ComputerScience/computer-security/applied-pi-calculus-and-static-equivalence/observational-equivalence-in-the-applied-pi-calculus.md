# Observational equivalence in the applied pi calculus

For closed extended processes of the [applied pi calculus](applied-pi-calculus.md), write $A \Downarrow a$ if $A$ can send a message on the name $a$, that is,
$A \to^* \equiv E[\overline a\langle M\rangle.P]$ for some evaluation context $E$ that does not bind $a$. An *observational bisimulation* is a symmetric relation $\mathcal R$ on
closed extended processes with the same domain such that $A \mathrel{\mathcal R} B$ implies

1. if $A \Downarrow a$ then $B \Downarrow a$;
2. if $A \to^* A'$ and $A'$ is closed, then $B \to^* B'$ and $A' \mathrel{\mathcal R} B'$ for some $B'$;
3. $E[A] \mathrel{\mathcal R} E[B]$ for all closing evaluation contexts $E$.

*Observational equivalence* $\approx$ is the largest observational bisimulation. It formalizes indistinguishability by an active attacker, modelled by the contexts.

## Depends on

- [The applied pi calculus](applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.1, Definition 4.1.
- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 5.3.2, Definition 5.1.

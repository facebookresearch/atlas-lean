# Hintikka set

A set $H$ of propositional formulas is a *Hintikka set* if

1. there is no propositional variable $P$ with $P \in H$ and $\neg P \in H$;
2. $\bot \notin H$ and $\neg\top \notin H$;
3. if $\neg\neg F \in H$, then $F \in H$;
4. if $\alpha \in H$, then $\alpha_1 \in H$ and $\alpha_2 \in H$;
5. if $\beta \in H$, then $\beta_1 \in H$ or $\beta_2 \in H$,

where $\alpha$, $\beta$ and their components are as in the classification of formulas for [propositional semantic tableaux](propositional-semantic-tableau.md).

## Depends on

- [Propositional semantic tableau](propositional-semantic-tableau.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.18, the definition of Hintikka sets, p. 98.

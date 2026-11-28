# Error threshold for a replicase encapsulated in protocells

**Model** (Bianconi, Zhao, Chen and Nowak 2013, mutation–selection–cell-division model). Sequences of two types live inside protocells. Type $A$ acts as a replicase and type $B$ does not. Every sequence replicates on its own; an $A$ copies without losing activity with probability $Q = (1 - \mu)^L$, where $\mu$ is the per-base error rate and $L$ the number of sites that must stay unchanged for activity, and otherwise produces a $B$. Back mutation $B \to A$ is neglected. A protocell containing $i$ sequences of type $A$ and $j$ of type $B$ divides when $i + j$ reaches a maximum size $M$, either into two daughter cells or into many (one sequence each). Four replicase types are distinguished by how the presence of $A$ raises replication rates inside the cell:

- $R_1$: one or more $A$ raises the rate of **all** sequences in the cell to $a > 1$;
- $R_2$: a single $A$ raises the rate of all **other** sequences to $a$ but not its own, while two or more $A$ raise every rate to $a$;
- $R_3$: with $i$ copies of $A$ the rate of all sequences is $1 + i\alpha$;
- $R_4$: with $i$ copies of $A$ the rate of the $B$ sequences is $1 + i\alpha$ and that of the $A$ sequences is $1 + (i - 1)\alpha$.

**Statement** (Bianconi, Zhao, Chen and Nowak 2013, Results and Discussion). For the commensal replicase $R_1$, whose benefit extends to itself, the condition for the replicase to be maintained takes the same form as the classical single-peak error threshold with the collective advantage $a$ of a replicase-bearing protocell in place of the individual fitness advantage of a master sequence: the replicase survives when $a Q > 1$, that is when

$$L < \frac{\log a}{-\log(1 - \mu)} \approx \frac{\log a}{\mu},$$

independently of the maximum cell size $M$ and of the division mode. For the altruistic replicase $R_2$, which does not help itself when alone, the threshold is strictly more demanding than for $R_1$, division into two is more permissive than division into many, and the maximal maintainable $L$ depends on $M$.

## Depends on

- [Error threshold](../../../eigen-s-quasispecies-error-threshold/master-equilibrium-pos-iff.md)

## Proof depends on

- [Maximal genome length](../../../eigen-s-quasispecies-error-threshold/one-lt-mul-pow-iff.md)

## Proof sketch

In the free-solution quasispecies the master sequence persists iff $\sigma Q > 1$, with $\sigma$ its relative fitness; the protocell result replaces competition among molecules by competition among cells, and the quantity that must exceed $1/Q$ is the advantage a cell gains from containing a replicase at all. For $R_1$ the advantage applies to every sequence in the cell including the replicase itself, so an $A$ never loses ground to the $B$ sequences it generates inside its own cell, and neither the group size $M$ nor how the cell splits changes the balance. For $R_2$ a lone replicase is at a disadvantage relative to its cellmates, which the group benefit has to overcome; binary fission keeps replicases together more often than fissioning into many vesicles, which is why it maintains more information, and larger $M$ then helps by making co-encapsulation of two replicases more likely.

## Sources

- G. Bianconi, K. Zhao, I. A. Chen and M. A. Nowak, "Selection for replicases in protocells", PLoS Computational Biology 9 (2013), e1003051, Results, Discussion and Materials and Methods ("The mutation-selection-cell division model", "The error threshold for replicase"), <https://doi.org/10.1371/journal.pcbi.1003051>, PMCID PMC3649988.

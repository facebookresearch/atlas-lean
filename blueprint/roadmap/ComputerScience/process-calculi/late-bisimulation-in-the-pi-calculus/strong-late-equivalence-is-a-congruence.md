# Strong late equivalence is a congruence

[Strong late equivalence](strong-late-equivalence.md) $\sim$ is a congruence for the operators of the π-calculus: it is an equivalence relation, and $P \sim Q$ implies $\alpha . P \sim \alpha . Q$ for every free action $\alpha$, $x(y) . P \sim x(y) . Q$, $P + R \sim Q + R$, $[x = y] P \sim [x = y] Q$, $P \mid R \sim Q \mid R$ and $(w) P \sim (w) Q$. More generally, for each distinction $D$, $\sim_D$ is an equivalence preserved by all these operators except input prefix, and $x(y) . P \sim_D x(y) . Q$ holds whenever $P \sim_D Q$ and $P\{v/y\} \sim_D Q\{v/y\}$ for every $v \in \mathrm{fn}(P, Q)$ with $(v, y) \in D$.

## Depends on

- [Strong late equivalence](strong-late-equivalence.md)

## Proof depends on

- [Strong late bisimilarity is an equivalence preserved by all operators except input prefix](late-bisimilarity-is-preserved-by-the-other-operators.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 4.1: Theorem 11 (properties of $\sim_D$) and Theorem 12 (strong equivalence is a congruence, the case $D = \emptyset$).

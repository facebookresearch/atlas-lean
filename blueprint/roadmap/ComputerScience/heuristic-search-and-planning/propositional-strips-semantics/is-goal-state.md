# Goal state of a STRIPS task

A STRIPS task over a type $\alpha$ of atoms has an initial state, finite sets $g^+, g^- \subseteq \alpha$ of positive and negative goal atoms, and a list of operators. A state $s$ (a finite set of true atoms) is a goal state when every positive goal atom is true and no negative goal atom is true:

$$g^+ \subseteq s \quad\text{and}\quad g^- \cap s = \emptyset .$$

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

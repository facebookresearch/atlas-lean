# Applicable STRIPS operator

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator $o$ is applicable in a state $s$ when every positive precondition holds and no negative precondition holds:

$$\mathrm{pre}^+(o) \subseteq s \quad\text{and}\quad \mathrm{pre}^-(o) \cap s = \emptyset .$$

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

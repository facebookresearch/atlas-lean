# Well-formed STRIPS operator

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator is well-formed when

$$\mathrm{pre}^+(o) \cap \mathrm{pre}^-(o) = \emptyset \quad\text{and}\quad \mathrm{add}(o) \cap \mathrm{del}(o) = \emptyset ,$$

so no atom is both required true and required false, and no atom is both added and deleted.

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

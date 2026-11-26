# Add-then-delete equals delete-then-add for disjoint effects

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. If $\mathrm{add}(o) \cap \mathrm{del}(o) = \emptyset$, then for every state $s$

$$(s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o) = (s \setminus \mathrm{del}(o)) \cup \mathrm{add}(o) .$$

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

# Total result of an applicable STRIPS operator

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator $o$ is applicable in $s$ when $\mathrm{pre}^+(o) \subseteq s$ and $\mathrm{pre}^-(o) \cap s = \emptyset$. Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. Its total result is $\mathrm{res}_o(s) = o(s)$ if $o$ is applicable in $s$, and $\mathrm{res}_o(s) = s$ otherwise. If $o$ is applicable in $s$, then $\mathrm{res}_o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$.

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

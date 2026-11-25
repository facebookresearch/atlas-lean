# Transitions of the total result STRIPS transition system

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator $o$ is applicable in $s$ when $\mathrm{pre}^+(o) \subseteq s$ and $\mathrm{pre}^-(o) \cap s = \emptyset$. Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. Its total result is $\mathrm{res}_o(s) = o(s)$ if $o$ is applicable in $s$, and $\mathrm{res}_o(s) = s$ otherwise. For a task with operator list $O$, the total result transition system has states as states and operators as labels. For all states $s, s'$ and every operator $o$, there is a transition $s \xrightarrow{o} s'$ if and only if $o \in O$ and $s' = \mathrm{res}_o(s)$.

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

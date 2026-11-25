# Strict goal reachability of a STRIPS task

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator $o$ is applicable in $s$ when $\mathrm{pre}^+(o) \subseteq s$ and $\mathrm{pre}^-(o) \cap s = \emptyset$. Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. Its total result is $\mathrm{res}_o(s) = o(s)$ if $o$ is applicable in $s$, and $\mathrm{res}_o(s) = s$ otherwise. A task consists of an initial state $s_0$, finite goal sets $g^+, g^- \subseteq \alpha$ and a list $O$ of operators; a state $s$ is a goal state when $g^+ \subseteq s$ and $g^- \cap s = \emptyset$. The strict transition system has states as states and operators as labels, with a transition $s \xrightarrow{o} s'$ when $o \in O$, $o$ is applicable in $s$ and $s' = o(s)$. A goal state is reachable when some goal state $s$ can be reached from $s_0$ by a finite sequence of transitions of the strict system.

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

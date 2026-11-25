# The empty STRIPS plan is valid iff the initial state is a goal

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). The operator $o$ is applicable in $s$ when $\mathrm{pre}^+(o) \subseteq s$ and $\mathrm{pre}^-(o) \cap s = \emptyset$. Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. Its total result is $\mathrm{res}_o(s) = o(s)$ if $o$ is applicable in $s$, and $\mathrm{res}_o(s) = s$ otherwise. A task consists of an initial state $s_0$, finite goal sets $g^+, g^- \subseteq \alpha$ and a list $O$ of operators; a state $s$ is a goal state when $g^+ \subseteq s$ and $g^- \cap s = \emptyset$. A plan $(o_1, \dots, o_n)$ totally executes from $s$ to $s'$ when there are states $s = t_0, t_1, \dots, t_n = s'$ with $o_i \in O$ and $t_i = \mathrm{res}_{o_i}(t_{i-1})$ for each $i$; an inapplicable operator is an identity step. A plan is valid when it totally executes from $s_0$ to a goal state. The empty plan is valid if and only if $s_0$ is a goal state.

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

# Membership in a progressed STRIPS state

Fix a type $\alpha$ of atoms. A state is a finite set $s \subseteq \alpha$ of true atoms. An operator $o$ consists of finite sets of atoms $\mathrm{pre}^+(o)$, $\mathrm{pre}^-(o)$ (positive and negative preconditions), $\mathrm{add}(o)$ and $\mathrm{del}(o)$ (add and delete lists). Its progression is $o(s) = (s \cup \mathrm{add}(o)) \setminus \mathrm{del}(o)$. For every state $s$ and atom $a$,

$$a \in o(s) \iff (a \in s \lor a \in \mathrm{add}(o)) \land a \notin \mathrm{del}(o) .$$

## Sources

T. Bylander, "The computational complexity of propositional STRIPS planning", *Artificial Intelligence* 69 (1994), Section 2.1.

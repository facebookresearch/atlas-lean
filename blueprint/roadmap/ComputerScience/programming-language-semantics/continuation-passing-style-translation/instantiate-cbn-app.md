# Administrative step of the call-by-name translation of an application

Let $\Xi$ be a
context and $W$, $V$, $Z$ types, and write $t^{\uparrow}$ for the weakening of a term $t$ by one
new newest variable. Let $F$ be a term of type
$((W \Rightarrow ((V \Rightarrow Z) \Rightarrow Z)) \Rightarrow Z) \Rightarrow Z$, $N$ a term of
type $W$ and $K$ a term of type $V \Rightarrow Z$, all in context $\Xi$. In the context $\Xi$
extended by a newest variable $k$ of type $V \Rightarrow Z$, consider the term
$F^{\uparrow}\,(\lambda p.\; p\; N^{\uparrow\uparrow}\; k)$. Here $p$ is the bound variable, of type
$W \Rightarrow ((V \Rightarrow Z) \Rightarrow Z)$, with de Bruijn index $0$, and $k$ has index $1$
under the binder. Instantiating $k$ with $K$ in this term gives
$F\,(\lambda p.\; p\; N^{\uparrow}\; K^{\uparrow})$.

# Typing judgment for the lambda calculus with references

The judgment
$\Gamma \mid S \vdash t : T$ (TAPL Figure 13-1), where the context $\Gamma$ lists the types of
the free de Bruijn variables (index $0$ first) and the store typing $S$ lists the types of the
locations $0, 1, \ldots$, is the least relation closed under the following rules, in which
$t : T$ abbreviates $\Gamma \mid S \vdash t : T$. A variable $x$ has type $T$ if $\Gamma$
assigns $T$ to index $x$. If $t$ has type $T_2$ in the context $\Gamma$ extended by $T_1$ at
index $0$ (with the same $S$), then $\lambda{:}T_1.\, t : T_1 \to T_2$. If $t_1 : T_1 \to T_2$
and $t_2 : T_1$, then $t_1\, t_2 : T_2$. The term $\mathtt{unit}$ has type $\mathrm{Unit}$. A
location $l$ has type $\mathrm{Ref}\, T$ if $S$ assigns $T$ to $l$. If $t : T$, then
$\mathrm{ref}\, t : \mathrm{Ref}\, T$. If $t : \mathrm{Ref}\, T$, then $!t : T$. If
$t_1 : \mathrm{Ref}\, T$ and $t_2 : T$, then $t_1 := t_2$ has type $\mathrm{Unit}$.

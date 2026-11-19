# The call-by-name CPS translation commutes with instantiation

Fix an answer type $R$ and
write $\overline{t}$ for the call-by-name CPS translation of a term $t$. Let $N$ be a term of type
$B$ in a context $A, \Gamma$ whose newest variable $x$ has type $A$, and let $a$ be a term of type
$A$ in context $\Gamma$. Then translating the instantiation $N[a/x]$ of $x$ by $a$ gives the
instantiation of the newest variable of $\overline{N}$ by $\overline{a}$:
$\overline{N[a/x]} = \overline{N}[\overline{a}/x]$.

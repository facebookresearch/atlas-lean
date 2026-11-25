# The call-by-name CPS translation commutes with weakening

Fix an answer type $R$ and write
$\overline{t}$ for the call-by-name CPS translation of a term $t$. For every term $t$ in a context
$\Gamma$ and every type $B$, translating the weakening of $t$ to the context $B, \Gamma$ (which
adds a fresh newest variable of type $B$) gives the weakening of $\overline{t}$ to the translated
context, which adds a fresh newest variable of the translated type
$(B^* \to R) \to R$, where $B^*$ is the call-by-name translation of $B$.

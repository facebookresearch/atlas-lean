# The call-by-name CPS translation commutes with substitution

Fix an answer type $R$ and
write $\overline{t}$ for the call-by-name CPS translation of a term $t$ and $\overline{x}$ for the
translation of a variable $x$, the variable at the same position of the translated context. Let
$\sigma$ be a substitution from a context $\Gamma$ to a context $\Delta$ (assigning to each
variable of $\Gamma$ a term of the same type in context $\Delta$), and let $\tau$ be a
substitution from the translated context of $\Gamma$ to that of $\Delta$ such that
$\tau(\overline{x}) = \overline{\sigma(x)}$ for every variable $x$ of $\Gamma$. Then for every
term $t$ in context $\Gamma$, $\overline{t[\sigma]} = \overline{t}[\tau]$.

# Single substitution cancels weakening

Let $t$ be a term of type $A$ in the typing context
$\Gamma$ and $a$ a term of type $B$ in context $\Gamma$. Weakening $t$ by a new newest variable of
type $B$ and then applying the substitution that replaces the newest variable by $a$ and leaves
every older variable unchanged gives back $t$.

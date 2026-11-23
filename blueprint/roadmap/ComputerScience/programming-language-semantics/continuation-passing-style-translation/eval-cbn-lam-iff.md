# The translation of an abstraction passes the translated function to its continuation

Fix an answer type $R$, and write $\overline{t}$ for the call-by-name CPS translation of a term
$t$, $T^*$ for the translation of a type $T$, and $\Gamma^*$ for the context obtained from
$\Gamma$ by replacing each type $C$ with $(C^* \to R) \to R$. Let $N$ be a term of type $B$ in
context $A, \Gamma$, let $K$ be a value of type $(A \to B)^* \to R$ in context $\Gamma^*$, and
let $w$ be a term of type $R$ in context $\Gamma^*$. Then $\overline{\lambda x.\,N}\,K$
evaluates to $w$ under call-by-value big-step evaluation if and only if
$K\,(\lambda x.\,\overline{N})$ does.

# Contextual equivalence in PCF

Write $C[s]$ for the term obtained by plugging $s$ into
the hole of a one-hole context $C$. PCF terms $t$ and $u$ of type $A$ in typing context $\Gamma$
are contextually equivalent when, for every one-hole context $C$ whose hole takes terms of type
$A$ in typing context $\Gamma$ and which produces closed terms of the ground type of natural
numbers, and for every natural number $n$, $C[t]$ evaluates to the numeral $n$ if and only if
$C[u]$ evaluates to the numeral $n$. Evaluation is big-step call-by-name evaluation.

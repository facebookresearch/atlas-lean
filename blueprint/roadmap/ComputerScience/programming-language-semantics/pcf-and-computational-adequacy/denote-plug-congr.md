# Equal denotations are preserved by plugging into PCF contexts

Let $t$ and $u$ be PCF
terms of type $A$ in typing context $\Gamma$ with the same denotation, and let $C$ be a one-hole
context whose hole takes terms of type $A$ in typing context $\Gamma$. Then the terms $C[t]$ and
$C[u]$ obtained by plugging $t$ and $u$ into the hole of $C$ have the same denotation.

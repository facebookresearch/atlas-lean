# Semantic equality is a congruence for typed contexts

Fix an interpretation $I$ of the
base types. Let $t$ and $u$ be terms of type $A$ in variable context $\Gamma$ that denote the same
value in $I$ under every semantic environment. Then for every typed one-hole context $C$ whose
hole has type $A$ in context $\Gamma$ and which produces a term of type $B$ in context $\Delta$, the
terms $C[t]$ and $C[u]$ obtained by plugging $t$ and $u$ into the hole also denote the same value
in $I$ under every semantic environment.

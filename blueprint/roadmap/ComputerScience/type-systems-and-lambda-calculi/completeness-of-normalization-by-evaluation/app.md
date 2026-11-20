# Related semantic functions send related arguments to related values

Let $f$ and $g$ be [related](related.md) semantic values of type $A \Rightarrow B$ in a context
$\Gamma$, let $\rho$ be a renaming from $\Gamma$ to a context $\Delta$, and let $a$ and $b$ be
[logical](logical.md) semantic values of type $A$ in $\Delta$ that are related. Then $f(\rho, a)$
and $g(\rho, b)$ are related at type $B$.

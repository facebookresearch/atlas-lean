# All Place Dual

Completed fibres of the dual of a line bundle at all places. Let $K$ be a field with an adelic
structure $A$ (`AdelicField`: places $v$ with complete normed completions $K_v$ and a measure
satisfying the product formula), $X$ a $K$-scheme, $L$ a line bundle on $X$ (`hL`) and $D$ an
algebraic dual of $L$ (`AlgebraicDual`): a line bundle $L^\vee$ with a map
$\mathrm{ev} : L \otimes L^\vee \to \mathcal{O}_X$ such that, for every sheaf of modules $T$,
$\phi \mapsto \mathrm{ev} \circ (1 \otimes \phi)$ is a bijection from maps $T \to L^\vee$ to maps
$L \otimes T \to \mathcal{O}_X$. Then, for every place $v$ and every point $p$ of $X_{K_v}$ with an
absolute value on its residue field extending that of $K_v$, there is an isomorphism, linear over
the completed residue field $\mathcal{H}(p)$, from the completed fibre of $L^\vee$ at $p$ to the
dual of the completed fibre of $L$ at $p$, that pairs the values at $p$ of local sections $t$ of
$L^\vee$ and $s$ of $L$ to the value at $p$ of $\mathrm{ev}(s \otimes t)$ (`AllPlaceDual`).

# Finite validity check for K

A modal formula $\varphi$ passes the finite check when,
for every nonempty set $U$ of subsets of the set $\mathrm{sub}(\varphi)$ of subformulas of
$\varphi$, every relation $R \subseteq U \times U$ and every $s \in U$, the formula $\varphi$
is true at $s$ in the Kripke model with set of worlds $U$, accessibility relation $R$, and an
atom $p$ true at a world $t$ iff $p \in t$; truth is computed by recursion on $\varphi$.

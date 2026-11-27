# Term-variable renaming in System F terms

For a renaming $\rho : \{0, \dots, m - 1\} \to \{0, \dots, k - 1\}$, the term-variable renaming of a [term](tm.md) $t \in \mathrm{Tm}_{n,m}$ is the term of $\mathrm{Tm}_{n,k}$ defined by $x_i \mapsto x_{\rho(i)}$, $\lambda A.\,b \mapsto \lambda A.\,b'$ where $b'$ renames $b$ by the [lifted renaming](lift-ren.md) $\rho^{\uparrow}$, and commuting with application, type abstraction and type application: only term binders lift the renaming.

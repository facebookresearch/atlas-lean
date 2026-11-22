# Type-variable renaming in System F terms

For a renaming $\rho : \{0, \dots, n - 1\} \to \{0, \dots, k - 1\}$, the type-variable renaming of a [term](tm.md) $t \in \mathrm{Tm}_{n,m}$ is its [type substitution](ty-subst.md) by $i \mapsto \alpha_{\rho(i)}$; term variables are unchanged.

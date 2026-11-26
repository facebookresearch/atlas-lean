# Reversing the parent list preserves tree ancestry

For a list $l$ of parent edges and vertices $a$, $d$: $a$ is a tree ancestor of $d$ for the reversed list exactly when it is for $l$, $\mathrm{TreeAncestor}(l^{\mathrm{rev}}, a, d) \iff \mathrm{TreeAncestor}(l, a, d)$.

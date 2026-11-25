# Counterexample-guided abstraction refinement

Let $M$ be a finite Kripke structure, $h$ a surjection onto the states of an abstraction $\hat M$ obtained by existential abstraction, and $\hat\pi = \hat s_1 \cdots \hat s_n$ an abstract counterexample path. Define $S_1 = h^{-1}(\hat s_1) \cap I$ and $S_{i+1} = \mathrm{Img}(S_i) \cap h^{-1}(\hat s_{i+1})$. Then $\hat\pi$ corresponds to a concrete path if and only if $S_n \ne \emptyset$. If $\hat\pi$ is spurious and $i$ is the least index with $S_{i+1} = \emptyset$, splitting the abstract state $\hat s_i$ into the *dead-end* states $S_i$ and the *bad* states of $h^{-1}(\hat s_i)$ that have a successor in $h^{-1}(\hat s_{i+1})$ (and the rest) gives a refined abstraction in which $\hat\pi$ is no longer a path. For an invariant $\mathbf{AG}\, p$ whose atomic propositions are respected by $h$, every counterexample is a finite path, and the loop that model checks $\hat M$, checks an abstract counterexample path as above and refines terminates, since every refinement strictly refines a partition of a finite set. It ends either with $\hat M \models \mathbf{AG}\, p$, and hence $M \models \mathbf{AG}\, p$, or with a concrete counterexample. General ACTL* properties have counterexamples that may be loops or trees, which need the further concretization and refinement cases of the source.

## Proof depends on

- [Existential abstraction preserves ACTL*](existential-abstraction-preserves-actl.md)

## Sources

- E. Clarke, O. Grumberg, S. Jha, Y. Lu and H. Veith, "Counterexample-guided abstraction refinement", *CAV 2000*, LNCS 1855, Springer, 2000

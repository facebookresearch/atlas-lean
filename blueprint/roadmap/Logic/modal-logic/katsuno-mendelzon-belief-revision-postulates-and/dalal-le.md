# Dalal's preorder on interpretations

Let $\sigma$ be a finite set of atoms with decidable equality, and represent each propositional formula over $\sigma$ by its finite set of models (interpretations $\sigma \to \{\mathrm{true}, \mathrm{false}\}$). The Dalal preorder relative to a model set $A$ puts $I$ before $J$ when the [Dalal key](dalal-key.md) of $I$ relative to $A$ is at most that of $J$. For nonempty $A$ this means that $I$ is at least as close to $A$ as $J$ in Hamming distance. For empty $A$ every key is $0$, so any two interpretations are related both ways.

# Valid IMP Hoare triples transfer to translated commands under an injective renaming

Let $\rho$ be an injective renaming from natural numbers to strings, $P$ and $Q$ predicates on IMP states and $c$ an IMP command such that the partial-correctness triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ is valid for IMP. Then the partial-correctness triple

$$\lbrace P \circ \pi_\rho \rbrace\ c_\rho\ \lbrace Q \circ \pi_\rho \rbrace$$

holds for the imperative language with arrays, where $c_\rho$ is the translation of $c$: whenever $c_\rho$ takes a state $s$ with $P(\pi_\rho(s))$ to a state $t$, $Q(\pi_\rho(t))$ holds. Termination is not asserted.

# Eval

Let $v \colon \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$ be a valuation of the atoms. The Boolean value $v(A)$ of a propositional formula $A$ is defined recursively by

$$v(p_n) = v(n), \quad v(A \to B) = \neg v(A) \vee v(B), \quad v(A \wedge B) = v(A) \wedge v(B),$$

$$v(A \vee B) = v(A) \vee v(B), \quad v(\neg A) = \neg v(A).$$

# Associative normal modal logic

An associative normal modal logic is a normal modal logic with one binary diamond $\circ$ that contains the associativity axiom $(p \circ q) \circ r \leftrightarrow p \circ (q \circ r)$; algebraically, its models are Boolean algebras with an associative normal binary operator.

**Definition.** The language $\mathcal L$ is given by $\varphi ::= p \mid \neg\varphi \mid \varphi \vee \varphi \mid \varphi \circ \varphi$ with $p$ from a countably infinite set of propositional variables (the source's countable set $\mathrm{Prop}$) and $\circ$ a binary diamond. $\mathbf K_2$ is the least normal modal logic in $\mathcal L$, and

$$
\mathbf{AK}_2 = \mathbf K_2 \oplus (p \circ q) \circ r \leftrightarrow p \circ (q \circ r)
$$

is the least normal modal logic containing the associativity axiom. A normal modal logic $\mathbf L$ in $\mathcal L$ is *associative* if $\mathbf L \supseteq \mathbf{AK}_2$.

*Algebras.* An *associative BAO* (Boolean semigroup) is a Boolean algebra with a binary operation $\circ$ that distributes over finite joins in each argument ($x \circ (y \vee z) = (x \circ y) \vee (x \circ z)$, $(x \vee y) \circ z = (x \circ z) \vee (y \circ z)$, $x \circ \bot = \bot \circ x = \bot$) and is associative. Every associative normal modal logic $\mathbf L$ is sound and complete for the variety $\mathsf V_{\mathbf L}$ of associative BAOs validating it, and $\varphi \in \mathbf L$ iff $\mathsf V_{\mathbf L} \models \varphi \approx \top$; so $\mathbf L$ is decidable iff the equational theory of $\mathsf V_{\mathbf L}$ is.

*Frames.* An *associative frame* is a set $X$ with a ternary relation $R$ such that for all $x, a, b, c$, there is $y$ with $Rxyc$ and $Ryab$ iff there is $z$ with $Rxaz$ and $Rzbc$; $x \models \varphi \circ \psi$ iff $Rxyz$ for some $y \models \varphi$ and $z \models \psi$. A binary operation $\cdot$ on a set $X$ (or a map $X^2 \to \mathcal P(X)$) gives the frame with $Rxyz$ iff $x = y \cdot z$ (respectively $x \in y \cdot z$); its *complex algebra* $(X, \cdot)^+$ is the powerset Boolean algebra with $Y \circ Z = \{x \mid x \in y \cdot z \text{ for some } y \in Y, z \in Z\}$ (Remarks 2.5 and 2.7 of the source; for a binary operation, $\{y \cdot z \mid y \in Y, z \in Z\}$). In particular $(\mathcal P(\mathbb N), \cup)$ is an associative frame, and $\mathrm{Log}(\mathcal P(\mathbb N), \cup)$ is the set of $\mathcal L$-formulas valid on it. $\mathbf{AK}_2$ is complete for the class of all associative frames, the associativity axiom being Sahlqvist.

## Depends on

- [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md)

## Proof depends on

None.

## Expansion

The correspondence between logics and varieties is the dual isomorphism $\mathbf L \mapsto \mathsf V_{\mathbf L}$ between normal extensions of $\mathbf{AK}_2$ and subvarieties of associative BAOs, with inverse $\mathsf V \mapsto \mathbf{AK}_2 \oplus \{\varphi \mid \mathsf V \models \varphi \approx \top\}$ (Proposition 2.3 of the source). Examples of associative frames are semigroups, semilattices, lattices, and the join-reduct $(B, \vee)$ of any Boolean algebra.

## Sources

- S. B. Knudstorp, "Diamonds and dominoes: impossibility results for associative modal logics", *The Journal of Symbolic Logic*, published online 2026, pp. 1–26, <https://doi.org/10.1017/jsl.2026.10256>; numbers from arXiv:2506.16366v2, <https://arxiv.org/abs/2506.16366v2>: Definitions 2.1, 2.2, 2.4 and 2.6, Remark 2.5 and Proposition 2.3.

# The Specker-Blatter theorem fails for a ternary relation

This result refutes the proposition stated as [The Specker-Blatter theorem for one ternary relation](specker-blatter-ternary.md). The statement is false: there are a first-order sentence $\varphi$ in the language of one ternary relation symbol and an integer $m \ge 1$ such that the counting function $f_\varphi$ is not ultimately periodic modulo $m$. Thus the Specker-Blatter theorem fails for ternary relations, already for first-order definable classes.

For a first-order sentence $\varphi$ in the language with one ternary relation symbol $R$ (with equality, no function symbols) and $n \in \mathbb{N}$, write $[n] = \{0, \dots, n-1\}$ and

$$f_\varphi(n) = \#\{A \subseteq [n]^3 : ([n], A) \models \varphi\},$$

the number of labelled structures on $[n]$ satisfying $\varphi$, where $R$ is interpreted by $A$. A sequence $s : \mathbb{N} \to \mathbb{N}$ is ultimately periodic modulo $m$ if there are $p \ge 1$ and $N$ with $s(n + p) \equiv s(n) \pmod m$ for all $n \ge N$.

## Sources

- J. A. Makowsky, Blatter-Specker Theorem for ternary relations, Open Problem Garden, http://www.openproblemgarden.org/op/blatter_specker_theorem_for_ternary_relations.
- E. Fischer and J. A. Makowsky, Extensions and limits of the Specker-Blatter theorem, J. Symb. Log. 89 (2024), 1284-1312, Theorems 6.3 and 12.10, arXiv:2206.12135, https://doi.org/10.1017/jsl.2024.17.

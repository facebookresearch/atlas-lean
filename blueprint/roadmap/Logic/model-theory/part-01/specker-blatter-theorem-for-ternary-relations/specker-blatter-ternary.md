# The Specker-Blatter theorem for one ternary relation

Statement (Open Problem Garden, J. A. Makowsky; Specker-Blatter theorem for one ternary relation, first-order case): for every first-order sentence $\varphi$ in the language of one ternary relation symbol and every integer $m \ge 1$, the counting function $f_\varphi$ is ultimately periodic modulo $m$.

For a first-order sentence $\varphi$ in the language with one ternary relation symbol $R$ (with equality, no function symbols) and $n \in \mathbb{N}$, write $[n] = \{0, \dots, n-1\}$ and

$$f_\varphi(n) = \#\{A \subseteq [n]^3 : ([n], A) \models \varphi\},$$

the number of labelled structures on $[n]$ satisfying $\varphi$, where $R$ is interpreted by $A$. A sequence $s : \mathbb{N} \to \mathbb{N}$ is ultimately periodic modulo $m$ if there are $p \ge 1$ and $N$ with $s(n + p) \equiv s(n) \pmod m$ for all $n \ge N$. It is false; the refutation is [The Specker-Blatter theorem fails for a ternary relation](specker-blatter-ternary-refuted.md).

## Sources

- J. A. Makowsky, Blatter-Specker Theorem for ternary relations, Open Problem Garden, http://www.openproblemgarden.org/op/blatter_specker_theorem_for_ternary_relations.

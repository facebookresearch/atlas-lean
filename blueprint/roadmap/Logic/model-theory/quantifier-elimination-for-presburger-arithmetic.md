# Quantifier elimination for Presburger arithmetic

Let $T_{\mathbb Z}$ be the theory of the integers in the language with the integer constants, $+$, $-$, $=$ and $<$, and let $\widehat T_{\mathbb Z}$ add, for every positive integer $k$, a unary predicate $k \mid \cdot$ with the axiom $\forall x\, (k \mid x \leftrightarrow \exists y\, x = k y)$, where $ky$ abbreviates $y + \dots + y$. Then $\widehat T_{\mathbb Z}$ admits quantifier elimination: every formula is equivalent in the integers to a quantifier-free formula with the same free variables, and Cooper's procedure computes one. Without the divisibility predicates quantifier elimination fails, since $\exists x\, 2x = y$ has no quantifier-free equivalent. Because quantifier-free sentences can be evaluated, the theory of $(\mathbb Z, 0, 1, +, <)$ is decidable, and so is Presburger arithmetic, the theory of $(\mathbb N, 0, 1, +)$, by relativizing quantifiers to $x \ge 0$.

## Sources

- Y.-F. Chen, "Quantifier elimination for Presburger arithmetic", lecture slides after I. Dillig, Formosan Summer School on Logic, Language, and Computation (FLOLAC), 2015, <https://flolac.iis.sinica.edu.tw/flolac15/_media/download:5-quantifier-elimination.pdf>
- D. C. Cooper, "Theorem proving in arithmetic without multiplication", *Machine Intelligence* 7:91–99, 1972
- M. Presburger, "Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer Zahlen, in welchem die Addition als einzige Operation hervortritt", *Comptes Rendus du I congrès de Mathématiciens des Pays Slaves*, 1929

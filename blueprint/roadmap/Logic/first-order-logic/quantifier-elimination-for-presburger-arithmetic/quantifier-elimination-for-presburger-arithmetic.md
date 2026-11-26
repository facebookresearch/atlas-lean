# Quantifier elimination for Presburger arithmetic

Let the Presburger language have the constant $0$, the successor $S$, addition $+$ and the order $<$, interpreted in $\mathbb N$. Every formula of this language is equivalent in $\mathbb N$ to a quantifier-free formula with the same free variables that is a Boolean combination of equalities $s = t$, inequalities $s < t$ and congruences $t \equiv r \pmod{m}$ with $m \ge 1$. The congruences are needed: $\exists y\, x = y + y$ is equivalent to no quantifier-free formula of the language itself. The elimination follows Cooper's procedure over the integers in the language with the integer constants, $+$, $-$, $<$ and the divisibility predicates $k \mid \cdot$, relativizing quantifiers to $x \ge 0$. Because quantifier-free sentences can be evaluated, the theory of $(\mathbb N, 0, S, +, <)$ is decidable.

## Sources

- Y.-F. Chen, "Quantifier elimination for Presburger arithmetic", lecture slides after I. Dillig, Formosan Summer School on Logic, Language, and Computation (FLOLAC), 2015, <https://flolac.iis.sinica.edu.tw/flolac15/_media/download:5-quantifier-elimination.pdf>
- D. C. Cooper, "Theorem proving in arithmetic without multiplication", *Machine Intelligence* 7:91–99, 1972
- M. Presburger, "Über die Vollständigkeit eines gewissen Systems der Arithmetik ganzer Zahlen, in welchem die Addition als einzige Operation hervortritt", *Comptes Rendus du I congrès de Mathématiciens des Pays Slaves*, 1929

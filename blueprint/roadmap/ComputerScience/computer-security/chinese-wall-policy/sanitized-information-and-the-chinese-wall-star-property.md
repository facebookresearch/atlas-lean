# Sanitized information and the Chinese Wall $*$-property

In the [Chinese Wall model](chinese-wall-model.md), fix a distinguished company dataset $y_o$ with its own conflict of interest class $x_o$.

- (Definition 2) An object $o_a$ contains *sanitized* information if $y_a = y_o$ and *unsanitized* information if $y_a \ne y_o$.
- (Axiom 5) An object bears the label $y_o$ if and only if it bears the label $x_o$.
- (Axiom 6, $*$-property) Write access to an object $o_b$ by a subject $s_u$ is permitted if and only if $N'(u, b)$ is true and there is no object $o_a$ with $N'(u, a)$
  true, which can be read by $s_u$, such that $y_a \ne y_b$ and $y_a \ne y_o$.

So a subject may write to an object only if every object it can read is either in the same company dataset or sanitized.

## Depends on

- [The Chinese Wall model](chinese-wall-model.md)

## Sources

- D. F. C. Brewer and M. J. Nash, "The Chinese Wall security policy", *Proceedings of the 1989 IEEE Symposium on Security and Privacy*, pp. 206–214, copy at <https://cgi.cse.unsw.edu.au/~meyden/3441/brewernash.pdf>: Annex A, "Sanitized information" (Definition 2 and Axioms 5–6), p. 213.

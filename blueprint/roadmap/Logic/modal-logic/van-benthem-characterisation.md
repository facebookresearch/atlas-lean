# Van Benthem's characterization theorem

The first-order modal language over a set of atoms has a binary relation symbol $R$ and a unary predicate $P_a$ for each atom $a$; a Kripke model $M = (W, R, V)$ interprets $R$ as accessibility and $P_a$ as the set of worlds where $a$ is true. A formula $\alpha(x)$ of this language with one free variable $x$ is bisimulation-invariant if for all Kripke models $M$ and $N$, every bisimulation $Z$ between them and all worlds $w$ of $M$ and $v$ of $N$ with $Z(w, v)$, $M \models \alpha[w]$ if and only if $N \models \alpha[v]$. The standard translation $ST_x(\varphi)$ of a modal formula is defined by $ST_x(a) = P_a(x)$, $ST_x(\bot) = \bot$, $ST_x(\varphi \to \psi) = ST_x(\varphi) \to ST_x(\psi)$ and $ST_x(\Box\varphi) = \forall y\,(R(x, y) \to ST_y(\varphi))$.

Statement: for every bisimulation-invariant first-order formula $\alpha(x)$ in one free variable over the modal language, there is a modal formula $\varphi$ such that for every Kripke model $M$ and every world $w$ of $M$,

$$M \models \alpha[w] \iff M \models ST_x(\varphi)[w].$$

This is the converse half of van Benthem's characterization theorem; the other half, that every standard translation is bisimulation-invariant, is not part of the statement.

## Sources

- J. van Benthem, "Modal Correspondence Theory", PhD thesis, University of Amsterdam, 1976, and "Modal Logic and Classical Logic", Bibliopolis, 1983; see also P. Blackburn, M. de Rijke, Y. Venema, Modal Logic, Cambridge University Press, 2001, §2.6, Theorem 2.68.

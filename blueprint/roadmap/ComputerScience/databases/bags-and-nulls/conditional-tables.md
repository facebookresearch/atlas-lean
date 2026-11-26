# Conditional tables

A condition is a conjunction of atoms $x = y$, $x = c$, $x \ne y$ and $x \ne c$, where $x, y$ are variables and $c$ a
constant; a valuation of the variables satisfies it when it makes the formula true. A conditional table (c-table) over
an attribute set is a triple $(T, P_T, \varphi)$ of a finite set $T$ of tuples whose entries are constants or
variables, a global condition $P_T$, and a local condition $\varphi_t$ for each tuple $t \in T$; conditions may mention
variables that occur in no tuple. Under the closed-world assumption it represents

$$\mathrm{rep}(T) = \{\{\nu(t) : t \in T,\ \nu \models \varphi_t\} : \nu \text{ a valuation with } \nu \models P_T\}.$$

A Codd table is a c-table with all conditions true in which no variable occurs twice; a naive table allows repeated
variables.

## Depends on

- [Incomplete databases, possible worlds and certain answers](incomplete-databases-possible-worlds-and-certain-answers.md)
- [Tuple](../relational-algebra/tuple.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 19.1 (pp. 488–489) and Section 19.3 with Figure 19.3 (pp. 493–494).

# Stratifications and the precedence graph of a Datalog program with negation

A Datalog program with negation ($\mathrm{datalog}^\neg$) allows negated atoms $\neg R(\bar v)$ and inequalities $x \ne y$ in rule bodies, under
active-domain semantics. It is *semipositive* if every negated relation in a rule body is extensional. Its
immediate consequence operator $T_P$ maps an instance $K$ over the schema of $P$ to the facts of $K$ over extensional
relations together with the heads $A$ of the ground rule instances $A \leftarrow L_1, \dots, L_n$ over the constants of $P$
and $K$ such that every positive relational literal $L_i$ is in $K$, every built-in equality or inequality literal holds as an equality or inequality of constants, and every negated relational literal $L_i = \neg B$ has $B \notin K$; unlike
the operator of a program without negation it need not be monotone.

A *stratification* of a $\mathrm{datalog}^\neg$ program $P$ is a sequence $P^1, \dots, P^n$ of programs, with a map $\sigma$
from the intensional relations of $P$ to $[1..n]$, such that (i) $\{P^1, \dots, P^n\}$ is a partition of $P$; (ii) all rules
defining a relation $R$ are in $P^{\sigma(R)}$; (iii) if $R(\bar u) \leftarrow \dots R'(\bar v) \dots$ is a rule and $R'$ is
intensional, then $\sigma(R') \le \sigma(R)$; and (iv) if $R(\bar u) \leftarrow \dots \neg R'(\bar v) \dots$ is a rule and $R'$
is intensional, then $\sigma(R') < \sigma(R)$. A program with a stratification is stratifiable.

The *precedence graph* $G_P$ has the intensional relations as nodes, a positive edge $(R', R)$ for each rule with head
relation $R$ and a positive body atom over an intensional relation $R'$, and a negative edge $(R', R)$ for each rule with head
relation $R$ and a negated body atom over an intensional relation $R'$; atoms over extensional relations and built-in
equalities give no edges.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the immediate consequence operator of a $\mathrm{datalog}^\neg$ program (p. 375), Definitions 15.2.1 and 15.2.4 and the definition of the precedence graph (pp. 377–380).

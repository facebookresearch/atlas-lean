# Truth of a prenex formula

Let $G$ be a group, $\varphi$ a quantifier-free formula in
conjunctive normal form, $q$ a finite list of Booleans read as a quantifier prefix ($\mathrm{true}$
for $\forall$, $\mathrm{false}$ for $\exists$), $i$ a natural number and $a \colon \mathbb{N} \to G$
an assignment of values to the variables $x_0, x_1, \dots$. Truth in $G$ under $a$ of the formula
with prefix $q$, whose first quantifier binds $x_i$, and matrix $\varphi$ is defined by recursion
on $q$. For the empty prefix it is truth of $\varphi$ in $G$ under $a$. For a prefix $\forall$
followed by $q'$, it holds when for every $g \in G$ the formula with prefix $q'$, whose first
quantifier binds $x_{i+1}$, holds under the assignment that agrees with $a$ except that $x_i$ takes
the value $g$; for a prefix $\exists$ followed by $q'$, the same holds for some $g \in G$. Thus the
quantifiers of $q$ bind $x_i, x_{i+1}, \dots$ in order, and the other variables keep their values
under $a$.

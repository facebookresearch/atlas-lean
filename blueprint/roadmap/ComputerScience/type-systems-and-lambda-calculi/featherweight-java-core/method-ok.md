# Well-formed methods

Fix a class table, a class declaration $cd$ and a named method declaration $(m, md)$, where $md$ has parameters $(C_1, x_1), \dots, (C_n, x_n)$, result class $C_0$ and body $e$. The method need not belong to $cd$ or $cd$ to the table: [class well-formedness](class-ok.md) checks each method listed in $cd$, and [table well-formedness](table-ok.md) checks each class listed in the table. The method is well formed (METHOD-OK) for $cd$ when:

1. the body $e$ has some type $A$ under the [typing context of the method](context-of.md), with $A$ a subtype of $C_0$; and
2. $m$ passes the [override check](override.md) against the superclass of $cd$ with parameter classes $C_1, \dots, C_n$ and result class $C_0$.

The typing context gives $\mathtt{this}$ the class of $cd$; any other variable gets the class of the first parameter with that name, and a variable that is not a parameter is unbound. No well-formedness of the table is assumed: a parameter named $\mathtt{this}$ is ignored, and of two parameters with the same name only the first counts.

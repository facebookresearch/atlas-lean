# Statements of the heap language

Statements of the heap language are built by six constructors, with variables identified by natural numbers: $\mathtt{skip}$; sequencing $s_1; s_2$; allocation $\mathtt{new}\ x\ \ell$, which stores in $x$ the address of [allocation site](site.md) $\ell$; copying $x := y$; loading $x := {*y}$, which stores in $x$ the address held at the address in $y$; and storing ${*x} := y$, which writes the address in $y$ at the address in $x$.

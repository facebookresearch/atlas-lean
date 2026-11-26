# Class names referenced by an expression

The class names that a Featherweight Java expression refers to form a list, with repeats kept, computed by recursion: a variable contributes the empty list; a field selection contributes the list of its receiver; a method invocation, the list of its receiver followed by that of its [argument list](class-refs-2.md); an object construction $\mathtt{new}\ C(\bar a)$, $C$ followed by the list of $\bar a$; and a cast $(C)\,e$, $C$ followed by the list of $e$. For example $(C)\,(C)\,x$ gives $[C, C]$.

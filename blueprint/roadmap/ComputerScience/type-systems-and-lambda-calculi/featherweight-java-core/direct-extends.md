# Direct superclass relation

For a class table and class names $C$ and $D$, $C$ directly extends $D$ when some declaration in the table has name $C$ and superclass $D$. Every declaration counts, not only the first declaration named $C$, which class lookup finds: a table with the entries $C$ extends $D$ and then $C$ extends $E$ has both edges.

## Sources

- Cornell University, CS 4110 Programming Languages and Logics, Lecture #30: Featherweight Java (Fall 2014), https://www.cs.cornell.edu/courses/cs4110/2014fa/lectures/lecture30.pdf.

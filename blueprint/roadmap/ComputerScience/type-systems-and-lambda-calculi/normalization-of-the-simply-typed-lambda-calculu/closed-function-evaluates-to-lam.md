# Closed functions evaluate to lambda abstractions

For every closed term $f$ of a function
type $A \Rightarrow B$ there is a term $b$ of type $B$ in the context with a single variable of
type $A$ such that $f$ reduces, in zero or more call-by-value steps, to the lambda abstraction
with body $b$.

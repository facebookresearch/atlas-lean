# The Davis-Putnam procedure

Given a CNF formula $\varphi$, eliminate the variables
that occur in $\varphi$ one after another, each exactly once, in the order of their first
occurrence in $\varphi$, each elimination being applied to the result of the previous one. The
procedure returns true if the resulting formula does not contain the empty clause, and false if
it does.

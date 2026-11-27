# Simultaneous substitution in an expression

Substitutes expressions for variables in a Featherweight Java expression according to the list `s` of (variable, expression) pairs, all at once: a variable is replaced by the expression of its first binding in `s` and is left unchanged when `s` has none, and the substitution is applied to field receivers, method receivers and arguments, constructor arguments and casts. Substituted expressions are not themselves substituted again. Used by the method invocation rule (E-INVK).

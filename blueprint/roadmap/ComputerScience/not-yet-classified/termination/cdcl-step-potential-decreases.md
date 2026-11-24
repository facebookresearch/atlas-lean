# Cdcl step potential decreases

Termination of the no-restart, no-deletion system over a
finite universe: fix finite sets `vars` of variables and
`clauses` of learnable clauses. The potential
`(clauses.card - L.card) * (vars.card + 1) + (vars.card -
t.length)` strictly decreases along every step taken from a
state whose trail variables lie in `vars`, whose trail decides
distinct variables, and whose learned clauses lie in `clauses`
(and likewise for the successor state), including learn steps
that backjump. Hence no infinite decide/learn sequence exists
within the universe: well-founded induction on the potential
bounds every run.

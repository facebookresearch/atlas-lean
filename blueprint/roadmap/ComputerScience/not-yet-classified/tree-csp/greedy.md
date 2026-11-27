# Greedy tree-CSP assignment

For a binary constraint problem with a parent map on its variables, a root-first order of the variables, domains of values in a nonempty type and a selection function choosing an element of a finite set (or failing), the greedy assignment visits the variables in order and gives each one the selected value among its domain values compatible with its parent's already chosen value (all domain values for a root). It fails as soon as some variable gets no selection, and otherwise returns the resulting assignment.

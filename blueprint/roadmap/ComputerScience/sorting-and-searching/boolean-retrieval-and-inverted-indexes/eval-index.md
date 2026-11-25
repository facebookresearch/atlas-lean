# Evaluating a Boolean query from postings lists

Given postings `index : α → List (Fin N)` for each term, a Boolean query is
evaluated to a set of documents: a term to the set of its postings, `and` to
the intersection, `or` to the union, and `not` to the complement in the set of
all `N` documents.

# Doubly-linked-list insertion (LIST-INSERT)

A store is an array of $n$ cells, each
either empty or holding a node with a payload and optional next and previous pointers to cells.
Given allocated cells $x$ and $y$ such that the successor of $y$, if any, is allocated,
inserting $x$ after $y$ performs the five lines of LIST-INSERT in order, each reading the store
as updated so far: set the next pointer of $x$ to the next pointer of $y$; set the previous
pointer of $x$ to $y$; test whether the next pointer of $y$ is NIL; if it is some cell $z$, set
the previous pointer of $z$ to $x$; set the next pointer of $y$ to $x$. The result is the
updated store, with cost one unit per pointer assignment and per NIL test.

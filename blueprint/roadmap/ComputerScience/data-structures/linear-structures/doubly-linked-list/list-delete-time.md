# Running time of doubly linked list deletion

Let the store be an array of cells, each
either empty or holding a node with optional next and previous pointers, let $h$ be the optional
head pointer, and let $x$ be a cell holding a node such that each cell named by its previous or
next pointer also holds a node. Counting one unit per NIL test and per executed pointer or head
assignment, deleting $x$ from the list with head $h$ costs exactly $4$ units if the node at $x$
has a next pointer, and exactly $3$ units otherwise.

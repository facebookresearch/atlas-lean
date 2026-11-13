# Inserting an array of items into a dynamic table

Given a dynamic table $T$ and an array
$x_0, \dots, x_{k-1}$ of items, the result of inserting the array into $T$ is obtained by starting
from $T$ and inserting $x_0, x_1, \dots, x_{k-1}$ one at a time with TABLE-INSERT, in array
order. Its cost is the sum of the costs of the $k$ insertions; for an empty array the result is
$T$ at cost $0$.

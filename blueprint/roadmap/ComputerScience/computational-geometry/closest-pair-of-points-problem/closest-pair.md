# Divide-and-conquer closest pair

Let $K$ be a field with a linear order. Given a list of
points in $K^2$, the closest-pair algorithm sorts the points by first coordinate (merge sort, at
no cost) and runs the closest-pair recursion on the sorted list. It returns a squared distance or
no value, and is charged one unit of cost per squared distance computed.

This is CLRS `CLOSEST-PAIR` (Section 33.4), with distances compared squared.

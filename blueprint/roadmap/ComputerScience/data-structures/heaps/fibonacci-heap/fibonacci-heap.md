# Fibonacci heap

A Fibonacci min-heap over a linearly ordered type consists of a list of
Fibonacci trees, each valid (heap-ordered, and at every node the stored degree equals the number
of children), together with a cached minimum equal to the least root value of these trees,
absent when the list is empty.

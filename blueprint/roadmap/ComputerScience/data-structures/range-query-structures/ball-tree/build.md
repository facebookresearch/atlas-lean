# Building a ball tree by halving

The ball tree built from a list of points of
$\mathbb{Z}^d$ is defined by recursion on the list. The empty list gives the empty tree and a
one-point list $[p]$ gives the leaf $p$. A list $L = [x_1, \dots, x_n]$ with $n \ge 2$ gives a
node whose center is $x_1$, whose bound is the squared radius of $L$ around $x_1$ (the largest
squared distance from $x_1$ to a point of $L$), whose left child is the tree built from the
first $\lfloor n/2 \rfloor$ points of $L$, and whose right child is the tree built from the
remaining points of $L$.

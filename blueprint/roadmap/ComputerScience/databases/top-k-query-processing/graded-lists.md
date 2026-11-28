# Graded sorted lists

A database of $N$ objects of a type $\alpha$ with $m$ attributes,
presented as $m$ sorted lists. The type $\alpha$ has exactly $N$ elements; when $m \ge 1$ this
also follows from the lists. Each object $x$ has a grade $x_i \in [0, 1]$ under each attribute
$i$. The list of attribute $i$ holds every object exactly once, as a bijection from the
positions $0, \ldots, N - 1$ to the objects, and its grades are nonincreasing along the
positions; objects with equal grades may appear in any order. Sorted access reads a list
position by position; random access gives the grade of any object under any attribute.

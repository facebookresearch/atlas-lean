# Correctness of the threshold algorithm for top-k aggregation

Let there be $N \ge 1$ distinct objects, $m \ge 1$ attributes, and an integer $k$ with $1 \le k \le N$.
For each attribute there is a list containing every object exactly once, in nonincreasing order of its grade
in $[0,1]$; equal grades may be ordered arbitrarily. Sorted access reads a list in that order, and random access
retrieves any object's grade for any attribute. Let $t : [0,1]^m \to \mathbb{R}$ be coordinatewise nondecreasing.

The threshold algorithm performs sorted access to the lists in parallel. For each object encountered, it retrieves
all its grades and computes its aggregate grade. It keeps the $k$ highest-graded distinct objects encountered so
far (or all of them if fewer than $k$ have been encountered), and stops when it has $k$ such objects with aggregate
grade at least $\tau = t(\underline{x}_1,\ldots,\underline{x}_m)$, where $\underline{x}_i$ is the last grade read
from list $i$.

It returns $k$ distinct objects each having aggregate grade at least that of every unreturned object. Ties in the
answer may be resolved arbitrarily; no particular global tie-breaking order is promised. For fixed $m$ and $k$,
the number of buffered object records and grades is bounded independently of $N$.

## Sources

- R. Fagin, A. Lotem and M. Naor, *Optimal aggregation algorithms for middleware*, J. Comput. System Sci. 66 (2003); arXiv:cs/0204046, §§1–2 (model and arbitrary ties), Theorems 4.1 and 4.2. <https://arxiv.org/abs/cs/0204046>

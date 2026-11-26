# Correctness of the threshold algorithm for top-k aggregation

Let there be $N \ge 1$ distinct objects, $m \ge 1$ attributes, and an integer $k$ with $1 \le k \le N$.
For each attribute $i$ there is a list containing every object exactly once, in nonincreasing order of its grade
$x_i \in [0,1]$ under that attribute; equal grades may be ordered arbitrarily. Sorted access reads a list in that
order, and random access retrieves any object's grade for any attribute. Let $t : \mathbb{R}^m \to \mathbb{R}$ be
nondecreasing in each coordinate on $[0,1]^m$ (only its values there are used), and call $t(x_1,\ldots,x_m)$ the
aggregate grade of an object with grades $x_1,\ldots,x_m$.

The threshold algorithm performs sorted access to the lists in parallel, in rounds: round $d+1$ reads the entry at
position $d$ of every list, counting positions from $0$. For each object read, it retrieves all its grades and
computes its aggregate grade. It keeps a buffer, empty at first: after each round, the buffer holds the $k$
highest-graded distinct objects among the old buffer and the objects just read (or all of them if there are fewer
than $k$), ties resolved arbitrarily. Between rounds it keeps only the number of rounds done and the buffer. It stops
after the first round at which the buffer holds $k$ objects with aggregate grade at least
$\tau = t(\underline{x}_1,\ldots,\underline{x}_m)$, where $\underline{x}_i$ is the last grade read from list $i$, and
returns the buffer. Fagin, Lotem and Naor state the stopping rule for all objects seen: at least $k$ objects seen so
far have aggregate grade at least $\tau$. The buffered form is used here so that every decision of the algorithm
depends only on its buffer and the round; by the first property below, the two forms hold after the same rounds.

Then, whatever the resolution of ties:

- after each round, the buffer holds the $k$ highest-graded distinct objects encountered so far, or all of them if
  fewer than $k$ have been encountered; in particular it never holds more than $k$ objects, however large $N$ is;
- after each round, the stopping rule holds exactly when at least $k$ of the objects encountered so far have
  aggregate grade at least $\tau$;
- the stopping rule holds after some round $d \le N$, so the algorithm stops after at most $N$ rounds;
- after every round at which the stopping rule holds, in particular the round at which the algorithm stops, the
  buffer consists of $k$ distinct objects each having aggregate grade at least that of every object outside it.

So the algorithm returns $k$ distinct objects each having aggregate grade at least that of every unreturned object.
Ties in the answer may be resolved arbitrarily; no particular global tie-breaking order is promised, and there may
be several such answers.

## Proof

Each round keeps the $k$ highest-graded objects among the old buffer and the new objects. Suppose the old buffer
holds the $k$ highest-graded objects seen, and some object seen earlier is left out of it. Then the old buffer is
full, the left-out object grades at most every object of the old buffer, and a new object enters the buffer only in
place of an old one of no higher grade; so the buffer stays the $k$ highest-graded objects seen. The two forms of
the stopping rule then agree: the buffer consists of objects seen; and if at least $k$ objects seen reach $\tau$,
the buffer is full, and were some buffered object below $\tau$, so would be every object seen but not buffered,
leaving fewer than $k$ objects seen that reach $\tau$. When the stopping rule holds after the round reading position
$p$, the buffer, which never holds more than $k$ objects, holds exactly $k$, all of aggregate grade at least $\tau$.
An object not yet seen sits after position $p$ in every list $i$, so its grade under attribute $i$ is at most
$\underline{x}_i$, and by monotonicity its aggregate grade is at most $\tau$; an object seen but not buffered grades
at most every buffered object. After round $N$ every object has been seen, so the buffer holds $k$ objects; every
object has every grade at least the last grade read from that list, so by monotonicity every object has aggregate
grade at least $\tau$, and the stopping rule holds.

## Sources

- R. Fagin, A. Lotem and M. Naor, *Optimal aggregation algorithms for middleware*, J. Comput. System Sci. 66 (2003),
  614–656; arXiv:cs/0204046, Section 1 (the model; ties broken arbitrarily), Section 2 (sorted and random access),
  and Section 4 (the threshold algorithm, Theorems 4.1 and 4.2). <https://arxiv.org/abs/cs/0204046>

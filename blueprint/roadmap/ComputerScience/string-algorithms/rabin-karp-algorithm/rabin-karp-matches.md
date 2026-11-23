# Rabin–Karp string matching

Given a base $d$, a modulus $q > 0$, a pattern
$P = p_0 \dots p_{m-1}$ and a text $T = t_0 \dots t_{n-1}$, both lists of natural numbers, this
returns the list, in increasing order, of all shifts $s$ with $s + m \le n$ and $t_{s+k} = p_k$
for every $k < m$. For $m \ge 1$ it computes by Horner's rule the residues modulo $q$ of $P$ and
of the first length-$m$ window of $T$, read as base-$d$ numerals, and updates the window residue
by a rolling hash; symbols are compared at a shift only when the two residues agree, from left to
right. If $m > n$ it returns the empty list. The empty pattern returns every shift
$0, 1, \dots, n$ at cost $0$.

The cost counts each executed multiplication, addition, subtraction and modulus in computing
the residues and $d^{m-1} \bmod q$, and each borrow test, residue equality test and symbol
equality test; shift-offset arithmetic and all other operations are free.

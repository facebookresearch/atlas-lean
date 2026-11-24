# Every permutation of 1, …, n can be sorted by reversals

For every natural number $n$ and every [permutation](uvalid.md) $\pi$ of $1, \dots, n$, written
as a list of integers, there is a natural number $k$ such that $\pi$ [sorts](usortable-in.md) to
$(1, \dots, n)$ in exactly $k$ reversals. Two reversals move the entry $n$ to the last
position, first to the front and then to the back, and the remaining list is sorted in the same
way (the pancake argument; Shamir and Peer, Lecture 11, §11.2).

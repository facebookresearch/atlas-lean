# Fixed points of free group automorphisms are decidable (Kourovka 10.25)

For every natural
number $r$ there is a computable function $f$ which takes the images of the $r$ free generators of
the free group $F_r$, each encoded as a word in the generators and their inverses, and returns a
Boolean, such that whenever the endomorphism $\varphi$ of $F_r$ sending each generator to its image
is bijective, $f$ returns true exactly when $\varphi(w) = w$ for some $w \neq 1$ in $F_r$.

The Kourovka Archive answers Problem 10.25 "Yes, it does", citing Bogopolski and Maslakova (2016),
who give an algorithm computing a basis of the fixed subgroup of an automorphism of a free group of
finite rank; the automorphism has a non-trivial fixed point exactly when that basis is nonempty.

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.25 (G. S. Makanin); resolution: O. Bogopolski and O. Maslakova, Int. J. Algebra Comput. 26, no. 1 (2016), 29-67, algorithm computing a basis of the fixed subgroup of an automorphism of a free group of finite rank; Kourovka Archive, Problem 10.25 ("Yes, it does").
